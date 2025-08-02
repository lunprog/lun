//! Checks for the SCIR like typechecking, safety checks etc

use std::iter::zip;

use lunc_diag::{ToDiagnostic, feature_todo};
use lunc_utils::{opt_unrecheable, symbol::Signedness};

use crate::diags::{
    ArityDoesntMatch, BreakFromLoopWithValue, BreakUseAnImplicitLabelInBlock, CallRequiresFuncType,
    CantContinueABlock, CantResolveComptimeValue, ExpectedPlaceExpression, ExpectedTypeFoundExpr,
    LabelKwOutsideLoopOrBlock, MismatchedTypes, TypeAnnotationsNeeded, UseOfUndefinedLabel,
};

use super::*;

impl SemaChecker {
    pub fn ck_mod(&mut self, module: &mut ScModule) {
        for item in &mut module.items {
            match self.ck_item(item) {
                Ok(()) => {}
                Err(d) => self.sink.emit(d),
            }
        }
    }

    /// Recursively pre check modules, it is used to add types and everything
    /// to global definitions and functions, but does not type check the body
    /// of functions
    pub fn pre_ck_module(&mut self, module: &mut ScModule) {
        for item in &mut module.items {
            match item {
                ScItem::GlobalDef { .. } => match self.pre_ck_global_def(item) {
                    Ok(()) => {}
                    Err(d) => self.sink.emit(d),
                },
                ScItem::Module { module, .. } => self.pre_ck_module(module),
            }
        }
    }

    /// # Safety
    ///
    /// This function must be called with a GlobalDef ScItem.
    fn pre_ck_global_def(&mut self, global_def: &mut ScItem) -> Result<(), Diagnostic> {
        let ScItem::GlobalDef {
            name: _,
            name_loc: _,
            mutable: _,
            typexpr,
            value,
            loc: _,
            sym: symref,
        } = global_def
        else {
            // SAFETY: it is the caller's responsibility to call this function
            // with a global definition
            opt_unrecheable!()
        };

        match &mut value.expr {
            ScExpr::FunDefinition {
                args,
                rettypexpr,
                body: _,
            } => {
                // function pre ck

                // we typecheck the type expression
                if let Some(typexpr) = &mut **typexpr {
                    self.ck_expr(typexpr, Some(Type::Type))?;

                    if typexpr.typ != Type::Type {
                        self.sink.emit(ExpectedTypeFoundExpr {
                            loc: typexpr.loc.clone().unwrap(),
                        })
                    }
                }

                // we evaluate the type expression
                let typexpr_as_type = if let Some(typexpr) = &mut **typexpr {
                    let value = self
                        .evaluate_expr(typexpr, Some(Type::Type))
                        .map_err(|loc| {
                            CantResolveComptimeValue {
                                loc_expr: typexpr.loc.clone().unwrap(),
                                loc,
                            }
                            .into_diag()
                        })?;

                    Some(value.as_type().unwrap_or(Type::Void))
                } else {
                    None
                };

                // collect the arguments types
                let mut args_typ = Vec::new();

                for ScArg {
                    typexpr: typexpr_arg,
                    sym: symref,
                    ..
                } in args
                {
                    match self.ck_expr(typexpr_arg, Some(Type::Type)) {
                        Ok(()) => {}
                        Err(d) => self.sink.emit(d),
                    }

                    let value_typ_arg = match self.evaluate_expr(typexpr_arg, Some(Type::Type)) {
                        Ok(typ) => typ,
                        Err(loc) => {
                            self.sink.emit(CantResolveComptimeValue {
                                loc_expr: typexpr_arg.loc.clone().unwrap(),
                                loc: loc.clone(),
                            });

                            ValueExpr::Type(Type::Void)
                        }
                    };

                    let arg_typ = match value_typ_arg.as_type() {
                        Some(typ) => typ,
                        None => {
                            self.sink.emit(ExpectedTypeFoundExpr {
                                loc: typexpr_arg.loc.clone().unwrap(),
                            });
                            Type::Void
                        }
                    };

                    args_typ.push(arg_typ.clone());

                    symref.set_typ(arg_typ);
                }

                // evaluate the return type expression
                let ret_typ = if let Some(ret_typexpr) = rettypexpr {
                    match self.ck_expr(ret_typexpr, Some(Type::Type)) {
                        Ok(()) => {}
                        Err(d) => self.sink.emit(d),
                    }

                    let value_typ_ret = match self.evaluate_expr(ret_typexpr, Some(Type::Type)) {
                        Ok(typ) => typ,
                        Err(loc) => {
                            self.sink.emit(CantResolveComptimeValue {
                                loc_expr: ret_typexpr.loc.clone().unwrap(),
                                loc: loc.clone(),
                            });

                            ValueExpr::Type(Type::Void)
                        }
                    };

                    match value_typ_ret.as_type() {
                        Some(typ) => typ,
                        None => {
                            self.sink.emit(ExpectedTypeFoundExpr {
                                loc: ret_typexpr.loc.clone().unwrap(),
                            });
                            Type::Void
                        }
                    }
                } else {
                    Type::Void
                };

                let typ = if let Some(ref typ) = typexpr_as_type {
                    typ.clone()
                } else {
                    Type::FunPtr {
                        args: args_typ,
                        ret: Box::new(ret_typ),
                    }
                };

                // we finally update the type of the symbol.
                symref.set_typ(typ);
            }
            _ => {
                // global def pre ck

                // we typecheck the type expression
                if let Some(typexpr) = &mut **typexpr {
                    self.ck_expr(typexpr, Some(Type::Type))?;

                    if typexpr.typ != Type::Type {
                        self.sink.emit(ExpectedTypeFoundExpr {
                            loc: typexpr.loc.clone().unwrap(),
                        })
                    }
                }

                // we evaluate the type expression
                let typexpr_as_type = if let Some(typexpr) = &mut **typexpr {
                    let value = self
                        .evaluate_expr(typexpr, Some(Type::Type))
                        .map_err(|loc| {
                            CantResolveComptimeValue {
                                loc_expr: typexpr.loc.clone().unwrap(),
                                loc,
                            }
                            .into_diag()
                        })?;

                    Some(value.as_type().unwrap_or(Type::Void))
                } else {
                    None
                };

                let typ = if let Some(ref typ) = typexpr_as_type {
                    typ.clone()
                } else {
                    Type::Unknown
                };

                // we finally update the type of the symbol.
                symref.set_typ(typ);
            }
        }

        Ok(())
    }

    pub fn ck_item(&mut self, item: &mut ScItem) -> Result<(), Diagnostic> {
        // reset the label stack
        self.label_stack.reset();

        match item {
            ScItem::GlobalDef {
                name: _,
                name_loc: _,
                mutable: _,
                typexpr,
                value,
                loc: _,
                sym: symref,
            } => {
                match &mut value.expr {
                    ScExpr::FunDefinition {
                        args: _,
                        rettypexpr,
                        body,
                    } => {
                        // set the function return type
                        self.fun_retty = symref
                            .typ()
                            .as_fun_ptr()
                            .expect("type should be a function pointer in a function definition")
                            .1;

                        self.fun_retty_loc =
                            rettypexpr.as_ref().and_then(|typexpr| typexpr.loc.clone());

                        // check the body of the function
                        self.ck_block(body, Some(self.fun_retty.clone()))?;

                        // check the type of the block of the function
                        if body.typ != self.fun_retty {
                            self.sink.emit(MismatchedTypes {
                                expected: vec![self.fun_retty.clone()],
                                found: body.typ.clone(),
                                due_to: self.fun_retty_loc.clone(),
                                note: None,
                                loc: body
                                    .last_expr
                                    .as_ref()
                                    .map(|expr| expr.loc.clone())
                                    .unwrap_or(body.loc.clone())
                                    .unwrap(),
                            });
                        }

                        // assign the type of the function
                        value.typ = symref.typ();

                        Ok(())
                    }
                    _ => {
                        let typ = symref.typ().as_option();

                        // we check the value of the definition
                        self.ck_expr(value, typ.clone())?;

                        // we check the type of the value
                        if value.typ == Type::Unknown {
                            self.sink.emit(TypeAnnotationsNeeded {
                                loc: value.loc.clone().unwrap(),
                            });
                        } else if let Some(typ) = &typ
                            && &value.typ != typ
                        {
                            self.sink.emit(MismatchedTypes {
                                expected: vec![typ],
                                found: value.typ.clone(),
                                due_to: typexpr.clone().unwrap().loc,
                                note: None,
                                loc: value.loc.clone().unwrap(),
                            });
                        } else if typ.is_none() {
                            // we set the type of the symbol to the type of the value as a fallback
                            // let mut
                            symref.set_typ(value.typ.clone());
                        }

                        // we evaluate the value of the global def
                        let value_expr = {
                            self.evaluate_expr(value, Some(symref.typ()))
                                .map_err(|loc| {
                                    CantResolveComptimeValue {
                                        loc_expr: value.loc.clone().unwrap(),
                                        loc,
                                    }
                                    .into_diag()
                                })?
                        };

                        symref.set_value(value_expr);

                        Ok(())
                    }
                }
            }
            ScItem::Module { module, .. } => {
                self.ck_mod(module);

                Ok(())
            }
        }
    }

    pub fn ck_expr(
        &mut self,
        expr: &mut ScExpression,
        mut coerce_to: Option<Type>,
    ) -> Result<(), Diagnostic> {
        if let Some(Type::Unknown) = coerce_to {
            coerce_to = None;
        }

        match &mut expr.expr {
            ScExpr::IntLit(_) => {
                if let Some(coercion) = coerce_to
                    && coercion.is_int()
                {
                    expr.typ = coercion;
                } else {
                    expr.typ = Type::I32;
                }
            }
            ScExpr::BoolLit(_) => {
                expr.typ = Type::Bool;
            }
            ScExpr::StringLit(_) => {
                // NOTE: string literals have a `*str` type.

                expr.typ = Type::Ptr {
                    mutable: false,
                    typ: Box::new(Type::Str),
                };
            }
            ScExpr::CharLit(_) => {
                expr.typ = Type::Char;
            }
            ScExpr::FloatLit(_) => {
                if let Some(coercion) = coerce_to
                    && coercion.is_float()
                {
                    expr.typ = coercion;
                } else {
                    expr.typ = Type::F32;
                }
            }
            ScExpr::Ident(symref) => {
                expr.typ = symref.typ();
            }
            ScExpr::Binary {
                lhs,
                op: BinOp::Assignment,
                rhs,
            } if lhs.is_underscore() => {
                self.ck_expr(rhs, Some(lhs.typ.clone()))?;

                expr.typ = Type::Void;
            }
            ScExpr::Binary {
                lhs,
                op: BinOp::Assignment,
                rhs,
            } => {
                self.ck_expr(lhs, None)?;
                self.ck_expr(rhs, Some(lhs.typ.clone()))?;

                if !lhs.is_place() {
                    self.sink.emit(ExpectedPlaceExpression {
                        loc: lhs.loc.clone().unwrap(),
                        lhs_assign: true,
                    });
                }

                expr.typ = Type::Void;
            }
            ScExpr::Binary { lhs, op, rhs } => {
                self.ck_expr(lhs, coerce_to.clone())?;
                self.ck_expr(rhs, coerce_to)?;

                if lhs.typ != Type::Unknown && lhs.typ != rhs.typ {
                    self.sink.emit(MismatchedTypes {
                        expected: vec![lhs.typ.clone()],
                        found: rhs.typ.clone(),
                        due_to: None,
                        note: None,
                        loc: rhs.loc.clone().unwrap(),
                    });
                } else if lhs.typ != rhs.typ {
                    self.sink.emit(MismatchedTypes {
                        expected: vec![rhs.typ.clone()],
                        found: lhs.typ.clone(),
                        due_to: None,
                        note: None,
                        loc: lhs.loc.clone().unwrap(),
                    });
                }

                expr.typ = if op.is_relational() || op.is_logical() {
                    Type::Bool
                } else if let Type::Unknown = lhs.typ {
                    rhs.typ.clone()
                } else {
                    lhs.typ.clone()
                };
            }
            ScExpr::Unary { op, expr: exp } => match op {
                UnaryOp::Negation => {
                    self.ck_expr(exp, coerce_to)?;

                    match (exp.typ.is_int(), exp.typ.signedness(), exp.typ.is_float()) {
                        (true, Some(Signedness::Unsigned), _) => {
                            self.sink.emit(MismatchedTypes {
                                expected: vec!["float", "integer"],
                                found: exp.typ.clone(),
                                due_to: None,
                                note: Some(format!(
                                    "can't perform a negation on an unsigned type like '{}'",
                                    exp.typ
                                )),
                                loc: exp.loc.clone().unwrap(),
                            });
                        }
                        (true, Some(Signedness::Signed), _) => {
                            expr.typ = exp.typ.clone();
                        }
                        (false, _, true) => {
                            expr.typ = exp.typ.clone();
                        }
                        _ => self.sink.emit(MismatchedTypes {
                            expected: vec!["float", "integer"],
                            found: exp.typ.clone(),
                            due_to: None,
                            note: None,
                            loc: exp.loc.clone().unwrap(),
                        }),
                    }
                }
                UnaryOp::Not => {
                    self.ck_expr(exp, Some(Type::Bool))?;

                    if exp.typ != Type::Bool {
                        self.sink.emit(MismatchedTypes {
                            expected: vec![Type::Bool],
                            found: exp.typ.clone(),
                            due_to: None,
                            note: None,
                            loc: exp.loc.clone().unwrap(),
                        });
                    }

                    expr.typ = Type::Bool;
                }
                UnaryOp::Dereference => {
                    // NOTE: here we tell the type checker `we if you have no idea try to coerce the expression to *T`.
                    self.ck_expr(
                        exp,
                        coerce_to.map(|t| Type::Ptr {
                            mutable: false,
                            typ: Box::new(t),
                        }),
                    )?;

                    expr.typ = if let Type::Ptr { mutable: _, typ } = &exp.typ {
                        *typ.clone()
                    } else {
                        return Err(MismatchedTypes {
                            expected: vec!["pointer"],
                            found: exp.typ.clone(),
                            due_to: None,
                            note: Some(format!("type '{}' cannot be dereferenced.", exp.typ)),
                            loc: exp.loc.clone().unwrap(),
                        }
                        .into_diag());
                    };
                }
            },
            ScExpr::AddressOf { mutable, expr: exp } => {
                let real_coerce = if let Some(Type::Ptr { mutable: _, typ }) = &coerce_to {
                    Some((**typ).clone())
                } else {
                    None
                };

                self.ck_expr(exp, real_coerce)?;

                expr.typ = Type::Ptr {
                    mutable: *mutable,
                    typ: Box::new(exp.typ.clone()),
                };
            }
            ScExpr::FunCall { callee, args } => {
                self.ck_expr(callee, None)?;

                let Type::FunPtr {
                    args: args_ty,
                    ret: ret_ty,
                } = &callee.typ
                else {
                    return Err(CallRequiresFuncType {
                        found: callee.typ.clone(),
                        loc: callee.loc.clone().unwrap(),
                    }
                    .into_diag());
                };

                if args_ty.len() != args.len() {
                    self.sink.emit(ArityDoesntMatch {
                        expected: args_ty.len(),
                        got: args.len(),
                        loc: callee.loc.clone().unwrap(),
                    });
                }

                for (arg, aty) in zip(args, args_ty) {
                    self.ck_expr(arg, Some(aty.clone()))?;

                    if arg.typ != *aty {
                        self.sink.emit(MismatchedTypes {
                            expected: vec![aty],
                            found: arg.typ.clone(),
                            due_to: None,
                            note: None,
                            loc: arg.loc.clone().unwrap(),
                        });
                    }
                }

                expr.typ = (**ret_ty).clone();
            }
            ScExpr::If {
                cond,
                then_br,
                else_br,
            } => {
                self.ck_expr(cond, Some(Type::Bool))?;

                if cond.typ != Type::Bool {
                    self.sink.emit(MismatchedTypes {
                        expected: vec![Type::Bool],
                        found: cond.typ.clone(),
                        due_to: None,
                        note: None,
                        loc: cond.loc.clone().unwrap(),
                    });
                }

                self.ck_expr(then_br, coerce_to)?;

                if let Some(else_br) = else_br {
                    self.ck_expr(else_br, Some(then_br.typ.clone()))?;

                    if else_br.typ != then_br.typ {
                        self.sink.emit(MismatchedTypes {
                            expected: vec![then_br.typ.clone()],
                            found: else_br.typ.clone(),
                            due_to: then_br.loc.clone(),
                            note: None,
                            loc: else_br.loc.clone().unwrap(),
                        });
                    }
                }

                expr.typ = then_br.typ.clone();
            }
            ScExpr::Block {
                label,
                block,
                index,
            } => {
                *index = Some(self.label_stack.define_label(label.clone(), false));

                self.ck_block(block, coerce_to)?;

                expr.typ = if let Some(LabelInfo { typ, .. }) =
                    self.label_stack.get_by_idx(index.unwrap())
                {
                    typ.clone().as_option().unwrap_or(block.typ.clone())
                } else {
                    block.typ.clone()
                };
            }
            ScExpr::Loop { label, body, index } => {
                // define label info
                *index = Some(self.label_stack.define_label(label.clone(), true));

                // check the body
                self.ck_block(body, None)?;

                if body.typ != Type::Void {
                    self.sink.emit(MismatchedTypes {
                        expected: vec![self.fun_retty.clone()],
                        found: body.typ.clone(),
                        due_to: self.fun_retty_loc.clone(),
                        note: None,
                        loc: body
                            .last_expr
                            .as_ref()
                            .map(|expr| expr.loc.clone())
                            .unwrap_or(body.loc.clone())
                            .unwrap(),
                    });
                }

                expr.typ = Type::Void;
            }
            ScExpr::Return { expr: exp } => {
                if let Some(exp) = exp {
                    self.ck_expr(exp, Some(self.fun_retty.clone()))?;

                    if exp.typ != self.fun_retty {
                        self.sink.emit(MismatchedTypes {
                            expected: vec![self.fun_retty.clone()],
                            found: exp.typ.clone(),
                            due_to: self.fun_retty_loc.clone(),
                            note: None,
                            loc: exp.loc.clone().unwrap(),
                        });
                    }
                } else if self.fun_retty != Type::Void {
                    self.sink.emit(MismatchedTypes {
                        expected: vec![self.fun_retty.clone()],
                        found: Type::Void,
                        due_to: self.fun_retty_loc.clone(),
                        note: None,
                        loc: expr.loc.clone().unwrap(),
                    });
                }

                expr.typ = Type::Noreturn;
            }
            ScExpr::Break {
                label,
                expr: exp,
                index,
            } => {
                // assign loop index
                let (typ, is_loop) = if let Some(label) = label {
                    let Some(LabelInfo {
                        index: idx,
                        typ,
                        is_loop,
                        ..
                    }) = self.label_stack.get_by_name(&label)
                    else {
                        return Err(UseOfUndefinedLabel {
                            name: label.clone(),
                            // TODO: add location of the label name
                            loc: expr.loc.clone().unwrap(),
                        }
                        .into_diag());
                    };

                    *index = Some(*idx);

                    (typ.clone(), *is_loop)
                } else {
                    let Some(LabelInfo {
                        index: idx,
                        typ,
                        is_loop,
                        ..
                    }) = self.label_stack.last()
                    else {
                        return Err(LabelKwOutsideLoopOrBlock {
                            kw: "break",
                            loc: expr.loc.clone().unwrap(),
                        }
                        .into_diag());
                    };

                    if !is_loop {
                        return Err(BreakUseAnImplicitLabelInBlock {
                            loc: expr.loc.clone().unwrap(),
                        }
                        .into_diag());
                    }

                    *index = Some(*idx);

                    (typ.clone(), *is_loop)
                };

                if let Some(exp) = exp {
                    self.ck_expr(exp, None)?;

                    if is_loop {
                        self.sink.emit(BreakFromLoopWithValue {
                            loc: expr.loc.clone().unwrap(),
                        });
                    } else if typ == Type::Unknown {
                        let info = self
                            .label_stack
                            .get_mut_by_idx(index.unwrap())
                            .expect("should've get a label info");

                        info.typ = exp.typ.clone();
                    } else {
                        let info = self
                            .label_stack
                            .get_by_idx(index.unwrap())
                            .expect("should've get a label info");

                        if info.typ != exp.typ {
                            self.sink.emit(MismatchedTypes {
                                expected: vec![info.typ.clone()],
                                found: exp.typ.clone(),
                                due_to: None,
                                note: None,
                                loc: exp.loc.clone().unwrap(),
                            });
                        }
                    }
                } else if typ == Type::Unknown {
                    let info = self
                        .label_stack
                        .get_mut_by_idx(index.unwrap())
                        .expect("should've get a label info");

                    info.typ = Type::Void;
                } else {
                    let info = self
                        .label_stack
                        .get_by_idx(index.unwrap())
                        .expect("should've get a label info");

                    self.sink.emit(MismatchedTypes {
                        expected: vec![info.typ.clone()],
                        found: Type::Void,
                        due_to: None,
                        note: None,
                        loc: expr.loc.clone().unwrap(),
                    });
                }

                expr.typ = Type::Noreturn;
            }
            ScExpr::Continue { label, index } => {
                // define the label index
                'blk: {
                    if let Some(label) = label {
                        let Some(LabelInfo {
                            index: idx,
                            is_loop,
                            ..
                        }) = self.label_stack.get_by_name(&label)
                        else {
                            self.sink.emit(UseOfUndefinedLabel {
                                name: label.clone(),
                                // TODO: add location of the label name
                                loc: expr.loc.clone().unwrap(),
                            });

                            break 'blk;
                        };

                        if !is_loop {
                            self.sink.emit(CantContinueABlock {
                                loc: expr.loc.clone().unwrap(),
                            });

                            break 'blk;
                        }

                        *index = Some(*idx);
                    } else {
                        let Some(LabelInfo {
                            index: idx,
                            is_loop,
                            ..
                        }) = self.label_stack.last()
                        else {
                            self.sink.emit(LabelKwOutsideLoopOrBlock {
                                kw: "continue",
                                loc: expr.loc.clone().unwrap(),
                            });

                            break 'blk;
                        };

                        if !is_loop {
                            self.sink.emit(CantContinueABlock {
                                loc: expr.loc.clone().unwrap(),
                            });

                            break 'blk;
                        }

                        *index = Some(*idx);
                    }
                }

                expr.typ = Type::Noreturn;
            }
            ScExpr::Null => {
                self.sink.emit(feature_todo! {
                    feature: "optional types are not yet implemented",
                    label: "'null' represent not having a value",
                    loc: expr.loc.clone().unwrap()
                });
            }
            ScExpr::MemberAccess { expr: _, member: _ } => {
                self.sink.emit(feature_todo! {
                    feature: "field access",
                    label: "field access, struct type definition are not yet implemented",
                    loc: expr.loc.clone().unwrap()
                });
            }
            ScExpr::QualifiedPath {
                path: _,
                sym: symref,
            } => {
                expr.typ = symref.typ();
            }
            ScExpr::Underscore => {
                // NOTE: we keep the typ unknown because the underscore
                // expression is only valid in lhs of assignment and we
                // have a special case for it.
            }
            ScExpr::FunDefinition { .. } => {
                self.sink.emit(feature_todo! {
                    feature: "inner function definition",
                    label: "function definition inside of a statement is not yet supported",
                    loc: expr.loc.clone().unwrap()
                });
            }
            ScExpr::PointerType {
                mutable: _,
                typexpr,
            } => {
                match self.ck_expr(typexpr, Some(Type::Type)) {
                    Ok(()) => {}
                    Err(d) => self.sink.emit(d),
                }

                if typexpr.typ != Type::Type {
                    self.sink.emit(ExpectedTypeFoundExpr {
                        loc: typexpr.loc.clone().unwrap(),
                    });
                }

                expr.typ = Type::Type;
            }
            ScExpr::FunPtrType { args, ret } => {
                for arg in args {
                    match self.ck_expr(arg, Some(Type::Type)) {
                        Ok(()) => {}
                        Err(d) => self.sink.emit(d),
                    }

                    if arg.typ != Type::Type {
                        self.sink.emit(ExpectedTypeFoundExpr {
                            loc: arg.loc.clone().unwrap(),
                        });
                    }
                }

                if let Some(ret) = ret {
                    match self.ck_expr(ret, Some(Type::Type)) {
                        Ok(()) => {}
                        Err(d) => self.sink.emit(d),
                    }

                    if ret.typ != Type::Type {
                        self.sink.emit(ExpectedTypeFoundExpr {
                            loc: ret.loc.clone().unwrap(),
                        });
                    }
                }

                expr.typ = Type::Type;
            }
        }

        Ok(())
    }

    pub fn ck_block(
        &mut self,
        block: &mut ScBlock,
        coerce_to: Option<Type>,
    ) -> Result<(), Diagnostic> {
        // check the statements
        for stmt in &mut block.stmts {
            match self.ck_stmt(stmt) {
                Ok(()) => {}
                Err(d) => self.sink.emit(d),
            }
        }

        // check the last expression
        block.typ = if let Some(expr) = &mut block.last_expr {
            self.ck_expr(expr, coerce_to)?;

            expr.typ.clone()
        } else {
            Type::Void
        };

        Ok(())
    }

    pub fn ck_stmt(&mut self, stmt: &mut ScStatement) -> Result<(), Diagnostic> {
        match &mut stmt.stmt {
            ScStmt::VariableDef {
                name: _,
                name_loc: _,
                mutable: _,
                typexpr,
                value,
                sym: symref,
            } => {
                // we typecheck the type expression
                if let Some(typexpr) = typexpr {
                    self.ck_expr(typexpr, Some(Type::Type))?;

                    if typexpr.typ != Type::Type {
                        self.sink.emit(ExpectedTypeFoundExpr {
                            loc: typexpr.loc.clone().unwrap(),
                        })
                    }
                }

                // we evaluate the type expression
                let typexpr_as_type = if let Some(typexpr) = typexpr {
                    let value = self
                        .evaluate_expr(typexpr, Some(Type::Type))
                        .map_err(|loc| {
                            CantResolveComptimeValue {
                                loc_expr: typexpr.loc.clone().unwrap(),
                                loc,
                            }
                            .into_diag()
                        })?;

                    Some(value.as_type().unwrap_or(Type::Void))
                } else {
                    None
                };

                // we check the value of the definition
                self.ck_expr(value, typexpr_as_type.clone())?;

                // we check the type of the value
                if value.typ == Type::Unknown {
                    self.sink.emit(TypeAnnotationsNeeded {
                        loc: value.loc.clone().unwrap(),
                    });
                } else if let Some(typ) = &typexpr_as_type
                    && &value.typ != typ
                {
                    self.sink.emit(MismatchedTypes {
                        expected: vec![typ],
                        found: value.typ.clone(),
                        due_to: typexpr.as_ref().unwrap().loc.clone(),
                        note: None,
                        loc: value.loc.clone().unwrap(),
                    });
                }

                let typ = if let Some(ref typ) = typexpr_as_type {
                    typ.clone()
                } else {
                    value.typ.clone()
                };

                // we finally update the type of the symbol.
                symref.set_typ(typ);
            }
            ScStmt::Defer { expr } | ScStmt::Expression(expr) => {
                self.ck_expr(expr, None)?;
            }
        }

        Ok(())
    }
}
