//! Block, Statement and Expression translator to CLIF.

use std::collections::HashMap;

use cranelift_codegen::ir::{
    BlockArg, InstBuilder, MemFlags, StackSlot, StackSlotData, StackSlotKind, Value,
    condcodes::{FloatCC, IntCC},
    types,
};
use cranelift_frontend::{FunctionBuilder, Variable};

use cranelift_module::{Linkage, Module};
use lunc_scir::{BinOp, ScBlock, ScExpr, ScExpression, ScStatement, ScStmt, UnaryOp};
use lunc_utils::{
    Span, opt_unreachable,
    symbol::{self, Signedness, SymKind},
};

use crate::{ClifGen, ClifId};

/// function definition translator
pub struct FunDefTranslator<'a> {
    /// function builder
    pub(crate) fb: FunctionBuilder<'a>,
    /// stack slots for the local variables
    pub(crate) slots: HashMap<symbol::Symbol, (StackSlot, types::Type)>,
    /// arg map. Maps the `which` of an argument symbol to the variable in the
    /// function
    pub(crate) args: Vec<Option<Variable>>,
    pub(crate) cgen: &'a mut ClifGen,
}

impl<'a> FunDefTranslator<'a> {
    /// Translate the block and return a value containing the returned value of
    /// the block.
    pub fn translate_block(&mut self, block: &ScBlock) -> Option<Value> {
        // translate every stmt
        for stmt in &block.stmts {
            self.translate_stmt(stmt);
        }

        // translate the last expr
        block
            .last_expr
            .as_ref()
            .and_then(|expr| self.try_translate_expr(expr))
    }

    /// Translate the expression and return the value containing it.
    ///
    /// # Panic
    ///
    /// This function will panic if called on an expression that can have a
    /// ZST type (like void or noreturn). So calling [try_translate_expr] is
    /// preferred if the expr may return a ZST.
    ///
    /// [try_translate_expr]: Self::try_translate_expr
    #[track_caller]
    pub fn translate_expr(&mut self, expr: &ScExpression) -> Value {
        self.try_translate_expr(expr)
            .expect("shouldn't be a ZST expression's type")
    }

    /// Translate the expression and return the value containing it.
    ///
    /// Returns `Some(..)` with the value, or `None` if the expression's type is
    /// a ZST like void or noreturn.
    pub fn try_translate_expr(&mut self, expr: &ScExpression) -> Option<Value> {
        match &expr.expr {
            ScExpr::IntLit(i) => {
                let imm = *i as i64;

                Some(self.fb.ins().iconst(self.cgen.lower_type(&expr.typ), imm))
            }
            ScExpr::BoolLit(b) => {
                let imm = symbol::bool_to_i8(*b) as i64;

                Some(self.fb.ins().iconst(self.cgen.lower_type(&expr.typ), imm))
            }
            ScExpr::StringLit(_) => {
                todo!("STRING LIT")
            }
            ScExpr::CStrLit(s) => {
                // build bytes for cstring, with a ZERO byte at the end.
                let mut bytes = Vec::with_capacity(s.len() + 1);
                bytes.extend_from_slice(s.as_bytes());
                bytes.push(0);

                // create a name for the symbol (should be unique)
                let Span { lo, hi, fid } = expr.loc.clone().unwrap();
                let name = format!(
                    "__cstr_{}_{}_{}_{}",
                    self.cgen.opts.orb_name(),
                    lo,
                    hi,
                    fid.as_usize()
                );

                // create the data
                let data_id = self.cgen.create_data(&name, Linkage::Local, false, bytes);
                let gv = self.cgen.module.declare_data_in_func(data_id, self.fb.func);

                let ptr_t = self.cgen.isa.pointer_type();
                Some(self.fb.ins().global_value(ptr_t, gv))
            }
            ScExpr::CharLit(c) => {
                let imm = *c as i64;

                Some(self.fb.ins().iconst(self.cgen.lower_type(&expr.typ), imm))
            }
            ScExpr::FloatLit(f) => {
                match expr.typ {
                    symbol::Type::F32 => {
                        let imm = *f as f32;
                        Some(self.fb.ins().f32const(imm))
                    }
                    symbol::Type::F64 => {
                        let imm = *f;
                        Some(self.fb.ins().f64const(imm))
                    }
                    symbol::Type::F16 | symbol::Type::F128 => {
                        todo!("float types are unstable")
                    }
                    // SAFETY: typechecking ensures it can only be a float type
                    _ => opt_unreachable!(),
                }
            }
            ScExpr::Ident(sym) => match sym.kind() {
                SymKind::Local { .. } => {
                    let (ss, typ) = *self.slots.get(sym).expect("undefined var");

                    Some(self.fb.ins().stack_load(typ, ss, 0))
                }
                SymKind::Arg => {
                    if let Some(var) = self.args[sym.which()] {
                        Some(self.fb.use_var(var))
                    } else {
                        None
                    }
                }
                SymKind::Function => {
                    let Some(ClifId::Func {
                        id,
                        sig: _,
                        arg_map: _,
                    }) = self.cgen.defs.get(sym)
                    else {
                        // SAFETY: should be a function.
                        opt_unreachable!()
                    };

                    let fun = self.cgen.module.declare_func_in_func(*id, self.fb.func);

                    Some(self.fb.ins().func_addr(self.cgen.isa.pointer_type(), fun))
                }
                kind => {
                    todo!("add support for symbol kind: {kind}")
                }
            },
            ScExpr::Binary {
                lhs,
                op: BinOp::Assignment,
                rhs,
            } => {
                let place = self.translate_place_expr(lhs);
                let val = self.translate_expr(rhs);

                self.fb.ins().store(MemFlags::new(), val, place, 0);

                None
            }
            ScExpr::Binary { lhs, op, rhs } => match lhs.typ {
                symbol::Type::I8
                | symbol::Type::I16
                | symbol::Type::I32
                | symbol::Type::I64
                | symbol::Type::I128
                | symbol::Type::Isz => {
                    Some(self.translate_integer_binop(lhs, op.clone(), rhs, Signedness::Signed))
                }
                symbol::Type::U8
                | symbol::Type::U16
                | symbol::Type::U32
                | symbol::Type::U64
                | symbol::Type::U128
                | symbol::Type::Usz => {
                    Some(self.translate_integer_binop(lhs, op.clone(), rhs, Signedness::Unsigned))
                }
                symbol::Type::F16 | symbol::Type::F32 | symbol::Type::F64 | symbol::Type::F128 => {
                    Some(self.translate_float_binop(lhs, op.clone(), rhs))
                }
                symbol::Type::Bool => Some(self.translate_bool_binop(lhs, op.clone(), rhs)),
                // SAFETY: type checking ensure it can only be int / float types
                _ => opt_unreachable!(),
            },
            ScExpr::FunCall { callee, args } => match &callee.expr {
                ScExpr::Ident(sym) if sym.kind() == SymKind::Function => {
                    let Some(ClifId::Func {
                        id,
                        sig: _,
                        arg_map: _,
                    }) = self.cgen.defs.get(sym)
                    else {
                        // SAFETY: should be a function.
                        opt_unreachable!()
                    };

                    let callee = self.cgen.module.declare_func_in_func(*id, self.fb.func);

                    let mut arg_vals = Vec::new();

                    for arg in args {
                        match self.try_translate_expr(arg) {
                            Some(val) => arg_vals.push(val),
                            None => {
                                // ZST arg we do nothing
                            }
                        }
                    }

                    let call = self.fb.ins().call(callee, &arg_vals);
                    let call_res = self.fb.inst_results(call);

                    debug_assert!(call_res.len() <= 1);

                    call_res.first().cloned()
                }
                _ => {
                    let fnptr = self.translate_expr(callee);
                    let (args_t, ret_t) = callee.typ.clone().as_fun_ptr().unwrap();

                    let (sig, _) = self.cgen.make_sig(&args_t, &ret_t);
                    let sigref = self.fb.import_signature(sig);

                    let mut arg_vals = Vec::new();

                    for arg in args {
                        match self.try_translate_expr(arg) {
                            Some(val) => arg_vals.push(val),
                            None => {
                                // ZST arg we do nothing
                            }
                        }
                    }

                    let call = self.fb.ins().call_indirect(sigref, fnptr, &arg_vals);
                    let call_res = self.fb.inst_results(call);

                    debug_assert!(call_res.len() <= 1);

                    call_res.first().cloned()
                }
            },
            _ => todo!(),
        }
    }

    /// Translates a [`ScExpression`] into a `Value` that **MUST** be a pointer
    /// to the place of the expression. It is used to translate for example,
    /// assignments.
    ///
    /// # UB
    ///
    /// `expr` must be a place, see [`ScExpression::is_place`]
    pub fn translate_place_expr(&mut self, expr: &ScExpression) -> Value {
        let ptr_t = self.cgen.isa.pointer_type();

        match &expr.expr {
            ScExpr::Ident(sym) => match sym.kind() {
                SymKind::Local { .. } => {
                    let (ss, _) = *self.slots.get(sym).expect("undefined var");

                    self.fb.ins().stack_addr(ptr_t, ss, 0)
                }
                SymKind::Global { .. } => {
                    todo!("global place expr translation");
                }
                // SAFETY: ensured to be a place by the caller
                _ => opt_unreachable!(),
            },
            ScExpr::Unary {
                op: UnaryOp::Dereference,
                expr,
            } => {
                // expr evaluates to a (mutable) pointer so we just translate
                // it like usual, note that here we know it will not be a ZST so
                // calling translate_expr is fine.

                self.translate_expr(expr)
            }
            // SAFETY: ensured to be a place by the caller
            _ => opt_unreachable!(),
        }
    }

    /// Translates a [`ScExpr::Binary`] for `bool` type.
    pub fn translate_bool_binop(
        &mut self,
        lhs: &ScExpression,
        op: BinOp,
        rhs: &ScExpression,
    ) -> Value {
        match op {
            BinOp::LogicalAnd => {
                // create BBs.
                let eval_y_bb = self.fb.create_block();
                let join_bb = self.fb.create_block();

                // evaluate lhs in current block.
                let x = self.translate_expr(lhs);

                // branch to `eval_y`(then) bb if x != 0
                // or to `join`(else) bb if x == 0
                let false_i8 = self.fb.ins().iconst(types::I8, 0);
                self.fb
                    .ins()
                    .brif(x, eval_y_bb, &[], join_bb, &[BlockArg::Value(false_i8)]);

                // build eval_y bb.
                {
                    self.fb.switch_to_block(eval_y_bb);

                    // evaluate rhs
                    let y = self.translate_expr(rhs);

                    // jump to join
                    self.fb.ins().jump(join_bb, &[BlockArg::Value(y)]);

                    // seal bb, we know it has no more predecessors
                    self.fb.seal_block(eval_y_bb);
                }

                // build join bb
                self.fb.switch_to_block(join_bb);
                self.fb.append_block_param(join_bb, types::I8);

                // seal bb, no more predecessors
                self.fb.seal_block(join_bb);

                self.fb.block_params(join_bb)[0]
            }
            BinOp::LogicalOr => {
                // create BBs.
                let eval_y_bb = self.fb.create_block();
                let join_bb = self.fb.create_block();

                // evaluate lhs in current block.
                let x = self.translate_expr(lhs);

                // branch to `eval_y`(then) bb if x != 0
                // or to `join`(else) bb if x == 0
                let true_i8 = self.fb.ins().iconst(types::I8, 1);
                self.fb
                    .ins()
                    .brif(x, eval_y_bb, &[], join_bb, &[BlockArg::Value(true_i8)]);

                // build eval_y bb.
                {
                    self.fb.switch_to_block(eval_y_bb);

                    // evaluate rhs
                    let y = self.translate_expr(rhs);

                    // jump to join
                    self.fb.ins().jump(join_bb, &[BlockArg::Value(y)]);

                    // seal bb, we know it has no more predecessors
                    self.fb.seal_block(eval_y_bb);
                }

                // build join bb
                self.fb.switch_to_block(join_bb);
                self.fb.append_block_param(join_bb, types::I8);

                // seal bb, no more predecessors
                self.fb.seal_block(join_bb);

                self.fb.block_params(join_bb)[0]
            }
            // SAFETY: it's up to the caller to guarantee that
            _ => opt_unreachable!(),
        }
    }

    /// Translates a [`ScExpr::Binary`] for an integer type with the given
    /// [`Signedness`].
    pub fn translate_integer_binop(
        &mut self,
        lhs: &ScExpression,
        op: BinOp,
        rhs: &ScExpression,
        sign: Signedness,
    ) -> Value {
        let x = self.translate_expr(lhs);
        let y = self.translate_expr(rhs);

        match op {
            BinOp::Add => self.fb.ins().iadd(x, y),
            BinOp::Sub => self.fb.ins().isub(x, y),
            BinOp::Mul => self.fb.ins().imul(x, y),
            BinOp::Div => match sign {
                Signedness::Unsigned => self.fb.ins().udiv(x, y),
                Signedness::Signed => self.fb.ins().sdiv(x, y),
            },
            BinOp::Rem => match sign {
                Signedness::Unsigned => self.fb.ins().urem(x, y),
                Signedness::Signed => self.fb.ins().srem(x, y),
            },
            BinOp::CompLT
            | BinOp::CompLE
            | BinOp::CompGT
            | BinOp::CompGE
            | BinOp::CompEq
            | BinOp::CompNe => {
                let cond = Self::translate_comp_op_to_int_cc(op, sign);

                self.fb.ins().icmp(cond, x, y)
            }
            // SAFETY: translated before.
            BinOp::Assignment => opt_unreachable!(),
            BinOp::LogicalAnd | BinOp::LogicalOr => unimplemented!("{op} unsupported for integers"),
            BinOp::BitwiseAnd => self.fb.ins().band(x, y),
            BinOp::BitwiseXor => self.fb.ins().bxor(x, y),
            BinOp::BitwiseOr => self.fb.ins().bor(x, y),
            BinOp::Shr => match sign {
                Signedness::Unsigned => self.fb.ins().ushr(x, y),
                Signedness::Signed => self.fb.ins().sshr(x, y),
            },
            BinOp::Shl => self.fb.ins().ishl(x, y),
        }
    }

    /// translates a comparison operator to an IntCC.
    ///
    /// # UB
    ///
    /// if `op` is something else than `Comp*`
    pub fn translate_comp_op_to_int_cc(op: BinOp, sign: Signedness) -> IntCC {
        match op {
            BinOp::CompLT => match sign {
                Signedness::Unsigned => IntCC::UnsignedLessThan,
                Signedness::Signed => IntCC::SignedLessThan,
            },
            BinOp::CompLE => match sign {
                Signedness::Unsigned => IntCC::UnsignedLessThanOrEqual,
                Signedness::Signed => IntCC::SignedLessThanOrEqual,
            },
            BinOp::CompGT => match sign {
                Signedness::Unsigned => IntCC::UnsignedGreaterThan,
                Signedness::Signed => IntCC::SignedGreaterThan,
            },
            BinOp::CompGE => match sign {
                Signedness::Unsigned => IntCC::UnsignedGreaterThanOrEqual,
                Signedness::Signed => IntCC::SignedGreaterThanOrEqual,
            },
            BinOp::CompEq => IntCC::Equal,
            BinOp::CompNe => IntCC::NotEqual,
            // SAFETY: caller is ensuring it is ok
            _ => opt_unreachable!(),
        }
    }

    /// Translates a [`ScExpr::Binary`] for floats types.
    pub fn translate_float_binop(
        &mut self,
        lhs: &ScExpression,
        op: BinOp,
        rhs: &ScExpression,
    ) -> Value {
        let x = self.translate_expr(lhs);
        let y = self.translate_expr(rhs);

        match op {
            BinOp::Add => self.fb.ins().fadd(x, y),
            BinOp::Sub => self.fb.ins().fsub(x, y),
            BinOp::Mul => self.fb.ins().fmul(x, y),
            BinOp::Div => self.fb.ins().fdiv(x, y),
            BinOp::CompLT
            | BinOp::CompLE
            | BinOp::CompGT
            | BinOp::CompGE
            | BinOp::CompEq
            | BinOp::CompNe => {
                let cond = Self::translate_comp_op_to_float_cc(op);

                self.fb.ins().fcmp(cond, x, y)
            }
            // SAFETY: translated before.
            BinOp::Assignment => opt_unreachable!(),
            BinOp::Rem
            | BinOp::LogicalAnd
            | BinOp::LogicalOr
            | BinOp::BitwiseAnd
            | BinOp::BitwiseXor
            | BinOp::BitwiseOr
            | BinOp::Shr
            | BinOp::Shl => {
                unimplemented!("{op} unsupported for floats")
            }
        }
    }

    /// translates a comparison operator to a FloatCC.
    ///
    /// # UB
    ///
    /// if `op` is something else than `Comp*`
    pub fn translate_comp_op_to_float_cc(op: BinOp) -> FloatCC {
        match op {
            BinOp::CompLT => FloatCC::LessThan,
            BinOp::CompLE => FloatCC::LessThanOrEqual,
            BinOp::CompGT => FloatCC::GreaterThan,
            BinOp::CompGE => FloatCC::GreaterThanOrEqual,
            BinOp::CompEq => FloatCC::Equal,
            BinOp::CompNe => FloatCC::NotEqual,
            // SAFETY: caller is ensuring it is ok
            _ => opt_unreachable!(),
        }
    }

    /// Translate a statement to CLIF instructions
    pub fn translate_stmt(&mut self, stmt: &ScStatement) {
        match &stmt.stmt {
            ScStmt::VariableDef { value, sym, .. } => {
                // 1. evaluate the value
                let value = self.translate_expr(value);

                let typ = sym.typ();
                let clif_typ = self.cgen.lower_type(&typ);
                let t_size = typ.size(self.cgen.opts.target().pointer_width().unwrap());

                // 2. create the stack slot
                let ss = self.fb.create_sized_stack_slot(StackSlotData::new(
                    StackSlotKind::ExplicitSlot,
                    t_size as u32,
                    t_size,
                ));

                // 3. add it to the stackslots map
                self.slots.insert(sym.clone(), (ss, clif_typ));

                // 4. store the value into the ss
                self.fb.ins().stack_store(value, ss, 0);
            }
            ScStmt::Defer { .. } => {
                todo!("DEFER")
            }
            ScStmt::Expression(expr) => {
                // it can be a ZST
                _ = self.try_translate_expr(expr);
            }
        }
    }
}
