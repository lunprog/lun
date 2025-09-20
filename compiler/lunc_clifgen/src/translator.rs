//! Block, Statement and Expression translator to CLIF.

use std::collections::HashMap;

use cranelift_codegen::ir::{InstBuilder, StackSlot, StackSlotData, StackSlotKind, Value, types};
use cranelift_frontend::FunctionBuilder;

use lunc_scir::{ScBlock, ScExpr, ScExpression, ScStatement, ScStmt};
use lunc_utils::{
    opt_unreachable,
    symbol::{self, SymKind},
};

use crate::ClifGen;

/// function definition translator
pub struct FunDefTranslator<'a> {
    pub(crate) fb: FunctionBuilder<'a>,
    pub(crate) stackslots: HashMap<symbol::Symbol, (StackSlot, types::Type)>,
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
            .map(|expr| self.translate_expr(expr))
    }

    /// Translate the expression and return the value containing it.
    pub fn translate_expr(&mut self, expr: &ScExpression) -> Value {
        match &expr.expr {
            ScExpr::IntLit(i) => {
                let imm = *i as i64;
                self.fb.ins().iconst(self.cgen.lower_type(&expr.typ), imm)
            }
            ScExpr::BoolLit(b) => {
                let imm = symbol::bool_to_i8(*b) as i64;
                self.fb.ins().iconst(self.cgen.lower_type(&expr.typ), imm)
            }
            ScExpr::StringLit(_) => {
                todo!("STRING LIT")
            }
            ScExpr::CharLit(c) => {
                let imm = *c as i64;
                self.fb.ins().iconst(self.cgen.lower_type(&expr.typ), imm)
            }
            ScExpr::FloatLit(f) => {
                match expr.typ {
                    symbol::Type::F32 => {
                        let imm = *f as f32;
                        self.fb.ins().f32const(imm)
                    }
                    symbol::Type::F64 => {
                        let imm = *f;
                        self.fb.ins().f64const(imm)
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
                    let (ss, typ) = *self.stackslots.get(sym).expect("undefined var");

                    self.fb.ins().stack_load(typ, ss, 0)
                }
                kind => {
                    todo!("add support for symbol kind: {kind}")
                }
            },
            _ => todo!(),
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
                self.stackslots.insert(sym.clone(), (ss, clif_typ));

                // 4. store the value into the ss
                self.fb.ins().stack_store(value, ss, 0);
            }
            ScStmt::Defer { .. } => {
                todo!("DEFER")
            }
            ScStmt::Expression(expr) => {
                _ = self.translate_expr(expr);
            }
        }
    }
}
