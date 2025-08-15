//! Checks for the SCIR like typechecking, safety checks etc

use std::iter::{self, zip};

use lunc_diag::{ToDiagnostic, feature_todo};
use lunc_utils::{
    opt_unreachable,
    symbol::{Signedness, Typeness},
};

use crate::diags::{
    ArityDoesntMatch, BorrowMutWhenNotDefinedMut, BreakUseAnImplicitLabelInBlock,
    BreakWithValueUnsupported, CallRequiresFuncType, CantContinueABlock, CantResolveComptimeValue,
    ExpectedPlaceExpression, ExpectedTypeFoundExpr, FunDeclOutsideExternBlock, FunctionInGlobalMut,
    ItemNotAllowedInExternBlock, LabelKwOutsideLoopOrBlock, MismatchedTypes, TypeAnnotationsNeeded,
    UseOfUndefinedLabel, WUnreachableCode, WUnusedLabel,
};

use super::*;

/// Used to emit the `unreachable_code` warning in block.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum NoreturnPos {
    /// The noreturn was in the statements of the block
    Statements {
        /// the position of the following statement that follows the first
        /// 'noreturn' statement
        pos: usize,
    },
    /// The noreturn is the last expression
    LastExpr,
}

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
        self.pre_ck_items(&mut module.items);
    }

    fn pre_ck_items(&mut self, items: &mut [ScItem]) {
        for item in items {
            match self.pre_ck_item(item) {
                Ok(()) => {}
                Err(d) => self.sink.emit(d),
            }
        }
    }

    fn pre_ck_item(&mut self, item: &mut ScItem) -> Result<(), Diagnostic> {
        match item {
            ScItem::GlobalDef { .. } => self.pre_ck_global_def(item),
            ScItem::FunDefinition {
                name: _,
                name_loc: _,
                typexpr,
                args,
                rettypexpr,
                body: _,
                defined_mut: _,
                loc: _,
                sym,
            } => {
                // function def pre ck

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
                    let value = self.evaluate_expr(typexpr).map_err(|(loc, note)| {
                        CantResolveComptimeValue {
                            note,
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

                    let value_typ_arg = match self.evaluate_expr(typexpr_arg) {
                        Ok(typ) => typ,
                        Err((loc, note)) => {
                            self.sink.emit(CantResolveComptimeValue {
                                note,
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

                    let value_typ_ret = match self.evaluate_expr(ret_typexpr) {
                        Ok(typ) => typ,
                        Err((loc, note)) => {
                            self.sink.emit(CantResolveComptimeValue {
                                note,
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
                sym.set_typ(typ);

                Ok(())
            }
            ScItem::FunDeclaration {
                name: _,
                name_loc: _,
                typexpr,
                args,
                rettypexpr,
                defined_mut: _,
                loc: _,
                sym,
            } => {
                // function decl pre ck

                // NOTE: we don't check if the container is ExternBlock here
                // because it will be checked later in `ck_item`.

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
                    let value = self.evaluate_expr(typexpr).map_err(|(loc, note)| {
                        CantResolveComptimeValue {
                            note,
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

                for arg in args {
                    match self.ck_expr(arg, Some(Type::Type)) {
                        Ok(()) => {}
                        Err(d) => self.sink.emit(d),
                    }

                    let value_typ_arg = match self.evaluate_expr(arg) {
                        Ok(typ) => typ,
                        Err((loc, note)) => {
                            self.sink.emit(CantResolveComptimeValue {
                                note,
                                loc_expr: arg.loc.clone().unwrap(),
                                loc: loc.clone(),
                            });

                            ValueExpr::Type(Type::Void)
                        }
                    };

                    let arg_typ = match value_typ_arg.as_type() {
                        Some(typ) => typ,
                        None => {
                            self.sink.emit(ExpectedTypeFoundExpr {
                                loc: arg.loc.clone().unwrap(),
                            });
                            Type::Void
                        }
                    };

                    args_typ.push(arg_typ.clone());
                }

                // evaluate the return type expression
                let ret_typ = if let Some(ret_typexpr) = rettypexpr {
                    match self.ck_expr(ret_typexpr, Some(Type::Type)) {
                        Ok(()) => {}
                        Err(d) => self.sink.emit(d),
                    }

                    let value_typ_ret = match self.evaluate_expr(ret_typexpr) {
                        Ok(typ) => typ,
                        Err((loc, note)) => {
                            self.sink.emit(CantResolveComptimeValue {
                                note,
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
                sym.set_typ(typ);

                Ok(())
            }
            ScItem::Module { module, .. } => {
                self.pre_ck_module(module);
                Ok(())
            }
            ScItem::ExternBlock { items, .. } => {
                self.pre_ck_items(items);
                Ok(())
            }
        }
    }

    /// # Safety
    ///
    /// This function must be called with a [`ScItem::GlobalDef`].
    fn pre_ck_global_def(&mut self, global_def: &mut ScItem) -> Result<(), Diagnostic> {
        let ScItem::GlobalDef {
            name: _,
            name_loc: _,
            mutable: _,
            typexpr,
            value: _,
            loc: _,
            sym: symref,
        } = global_def
        else {
            // SAFETY: it is the caller's responsibility to call this function
            // with a global definition
            opt_unreachable!()
        };

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
            let value = self.evaluate_expr(typexpr).map_err(|(loc, note)| {
                CantResolveComptimeValue {
                    note,
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

        Ok(())
    }

    /// Block type checking
    pub fn block_typeck(
        &mut self,
        expected: &Type,
        found: &mut ScBlock,
        due_to: impl Into<OSpan>,
        note: impl Into<Option<String>>,
        other_loc: impl Into<OSpan>,
    ) {
        if *expected != found.typ {
            if found.typ.can_coerce(expected) {
                // NOTE: here unlike `expr_typeck` we don't need to apply the type.
                return;
            }

            self.sink.emit(MismatchedTypes {
                expected: vec![expected.clone()],
                found: found.typ.clone(),
                due_to: due_to.into(),
                notes: note.into().as_slice().to_vec(),
                loc: other_loc.into().unwrap_or(found.loc.clone().unwrap()),
            });
        }
    }

    /// Expression type checking
    pub fn expr_typeck(
        &mut self,
        expected: &Type,
        found: &mut ScExpression,
        due_to: impl Into<Option<Span>>,
        note: impl Into<Option<String>>,
    ) {
        if *expected != found.typ {
            if found.typ.can_coerce(expected)
                && Self::apply_typ_on_expr(found, expected.clone()).is_some()
            {
                return;
            }

            let mut notes = note.into().as_slice().to_vec();

            // special case for if, we add a note.
            if matches!(
                &found.expr,
                ScExpr::If {
                    cond: _,
                    then_br: _,
                    else_br: None
                }
            ) {
                notes.push(
                    "an if expression without an else branch evaluates to type 'void'".to_string(),
                );

                notes.push(format!(
                    "consider adding an else branch that evaluates to type '{expected}'",
                ));
            }

            self.sink.emit(MismatchedTypes {
                expected: vec![expected.clone()],
                found: found.typ.clone(),
                due_to: due_to.into(),
                notes,
                loc: found.loc.clone().unwrap(),
            });
        }
    }

    /// Tries to apply a new type to the `expr`, does not check that the
    /// expression can have this type.
    #[must_use]
    pub fn apply_typ_on_expr(expr: &mut ScExpression, typ: Type) -> Option<()> {
        match &mut expr.expr {
            ScExpr::IntLit(_) => {}
            ScExpr::FloatLit(_) => {}
            ScExpr::Ident(symref) if symref.typeness() == Typeness::Implicit => {
                symref.inspect_mut(|sym| {
                    sym.typ = typ.clone();
                    sym.typeness = Typeness::Explicit;
                });
            }
            ScExpr::Binary { lhs, op: _, rhs } => {
                Self::apply_typ_on_expr(lhs, typ.clone())?;
                Self::apply_typ_on_expr(rhs, typ.clone())?;
            }
            ScExpr::Unary { op: _, expr } | ScExpr::Borrow { mutable: _, expr } => {
                Self::apply_typ_on_expr(expr, typ.clone())?;
            }
            ScExpr::If {
                cond: _,
                then_br,
                else_br,
            } => {
                Self::apply_typ_on_expr(then_br, typ.clone())?;

                if let Some(else_br) = else_br {
                    Self::apply_typ_on_expr(else_br, typ.clone())?;
                }
            }
            ScExpr::Block {
                block,
                label: _,
                index,
            } => {
                for stmt in &mut block.stmts {
                    match &mut stmt.stmt {
                        ScStmt::Expression(ScExpression {
                            expr:
                                ScExpr::Break {
                                    label: _,
                                    expr: Some(expr),
                                    index: index_break,
                                },
                            typ: _,
                            loc: _,
                        }) if index_break == index => {
                            Self::apply_typ_on_expr(expr, typ.clone())?;
                        }
                        _ => {}
                    }
                }

                if let Some(last) = &mut block.last_expr {
                    Self::apply_typ_on_expr(last, typ.clone())?;
                }
            }
            _ => return None,
        }

        expr.typ = typ;

        Some(())
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
                    self.expr_typeck(
                        typ,
                        value,
                        (**typexpr)
                            .as_ref()
                            .map(|exp| exp.loc.as_ref().unwrap().clone()),
                        None,
                    );
                } else if typ.is_none() {
                    // we set the type of the symbol to the type of the value as a fallback
                    // let mut
                    symref.set_typ(value.typ.clone());
                }

                // we evaluate the value of the global def
                let value_expr = {
                    self.evaluate_expr(value).map_err(|(loc, note)| {
                        CantResolveComptimeValue {
                            note,
                            loc_expr: value.loc.clone().unwrap(),
                            loc,
                        }
                        .into_diag()
                    })?
                };

                symref.set_value(value_expr);

                Ok(())
            }
            ScItem::FunDefinition {
                name: _,
                name_loc: _,
                typexpr: _,
                args: _,
                rettypexpr,
                body,
                defined_mut,
                loc,
                sym,
            } => {
                // emit an error
                if *defined_mut {
                    self.sink.emit(FunctionInGlobalMut {
                        fun: "function definition",
                        loc: loc.clone().unwrap(),
                    })
                }

                // set the function return type

                self.fun_retty = sym.typ().as_fun_ptr().map(|t| t.1).unwrap_or(Type::Void);
                // unwrap with a dummy if the type was defined to a non-fnptr.

                self.fun_retty_loc = rettypexpr.as_ref().and_then(|typexpr| typexpr.loc.clone());

                // check the body of the function
                self.ck_block(body, Some(self.fun_retty.clone()))?;

                // check the type of the block of the function
                self.block_typeck(
                    &self.fun_retty.clone(),
                    body,
                    self.fun_retty_loc.clone(),
                    None,
                    body.last_expr
                        .as_ref()
                        .map(|expr| expr.loc.clone())
                        .unwrap_or(body.loc.clone())
                        .unwrap(),
                );

                Ok(())
            }
            ScItem::FunDeclaration {
                defined_mut, loc, ..
            } if self.container == ItemContainer::ExternBlock => {
                // emit an error
                if *defined_mut {
                    self.sink.emit(FunctionInGlobalMut {
                        fun: "function declaration",
                        loc: loc.clone().unwrap(),
                    })
                }

                Ok(())
            }
            ScItem::FunDeclaration {
                defined_mut, loc, ..
            } => {
                // fundecl must be inside of an extern block..

                self.sink.emit(FunDeclOutsideExternBlock {
                    loc: loc.clone().unwrap(),
                });

                // emit an error
                if *defined_mut {
                    self.sink.emit(FunctionInGlobalMut {
                        fun: "function declaration",
                        loc: loc.clone().unwrap(),
                    })
                }

                Ok(())
            }
            ScItem::Module { module, .. } => {
                self.ck_mod(module);

                Ok(())
            }
            ScItem::ExternBlock { abi: _, items, loc } => {
                let container = self.container.clone();
                self.container = ItemContainer::ExternBlock;

                let old_items = items.clone();
                let mut new_items = Vec::with_capacity(old_items.len());

                for item in old_items {
                    match item {
                        ScItem::FunDeclaration { .. } => {
                            // function declaration are allowed in an extern block
                            new_items.push(item);
                        }
                        ScItem::FunDefinition { .. } => {
                            self.sink.emit(ItemNotAllowedInExternBlock {
                                item: "function definition",
                                note: None,
                                loc: item.loc(),
                                extern_block_loc: loc.clone().unwrap(),
                            });
                        }
                        ScItem::GlobalDef { .. } => {
                            self.sink.emit(ItemNotAllowedInExternBlock {
                                item: "global definition",
                                note: None,
                                loc: item.loc(),
                                extern_block_loc: loc.clone().unwrap(),
                            });
                        }
                        ScItem::Module { .. } => {
                            self.sink.emit(ItemNotAllowedInExternBlock {
                                item: "module",
                                note: None,
                                loc: item.loc(),
                                extern_block_loc: loc.clone().unwrap(),
                            });
                        }
                        ScItem::ExternBlock { .. } => {
                            self.sink.emit(ItemNotAllowedInExternBlock {
                                item: "extern block",
                                note: Some("you probably want to un nest the extern block"),
                                loc: item.loc(),
                                extern_block_loc: loc.clone().unwrap(),
                            });
                        }
                    }
                }

                *items = new_items;

                for item in items {
                    match self.ck_item(item) {
                        Ok(()) => {}
                        Err(d) => self.sink.emit(d),
                    }
                }

                self.container = container;

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

                if let Some(note) = lhs.is_place() {
                    self.sink.emit(ExpectedPlaceExpression {
                        note: Some(note),
                        lhs_assign: true,
                        loc: lhs.loc.clone().unwrap(),
                    });
                }

                expr.typ = Type::Void;
            }
            ScExpr::Binary { lhs, op, rhs } => {
                self.ck_expr(lhs, coerce_to.clone())?;
                self.ck_expr(rhs, coerce_to)?;

                if lhs.typ != Type::Unknown && lhs.typ != rhs.typ {
                    self.expr_typeck(&lhs.typ, rhs, None, None);
                } else if lhs.typ != rhs.typ {
                    self.expr_typeck(&rhs.typ, lhs, None, None);
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
                                expected: vec!["float", "signed integer"],
                                found: exp.typ.clone(),
                                due_to: None,
                                notes: vec![format!(
                                    "can't perform a negation on an unsigned type like '{}'",
                                    exp.typ
                                )],
                                loc: exp.loc.clone().unwrap(),
                            });

                            // we set the type to a dummy type to avoid having
                            // E012 diag.
                            expr.typ = exp.typ.clone();
                        }
                        (true, Some(Signedness::Signed), _) => {
                            expr.typ = exp.typ.clone();
                        }
                        (false, _, true) => {
                            expr.typ = exp.typ.clone();
                        }
                        _ => {
                            self.sink.emit(MismatchedTypes {
                                expected: vec!["float", "signed integer"],
                                found: exp.typ.clone(),
                                due_to: None,
                                notes: vec![],
                                loc: exp.loc.clone().unwrap(),
                            });

                            // we set the type to a dummy type to avoid having
                            // E012 diag.
                            expr.typ = exp.typ.clone();
                        }
                    }
                }
                UnaryOp::Not => {
                    self.ck_expr(exp, Some(Type::Bool))?;

                    self.expr_typeck(&Type::Bool, exp, None, None);

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
                        self.sink.emit(MismatchedTypes {
                            expected: vec!["pointer"],
                            found: exp.typ.clone(),
                            due_to: None,
                            notes: vec![format!("type '{}' cannot be dereferenced.", exp.typ)],
                            loc: exp.loc.clone().unwrap(),
                        });

                        // we set a dummy type
                        Type::Void
                    };
                }
            },
            ScExpr::Borrow { mutable, expr: exp } => {
                let real_coerce = if let Some(Type::Ptr { mutable: _, typ }) = &coerce_to {
                    Some((**typ).clone())
                } else {
                    None
                };

                self.ck_expr(exp, real_coerce)?;

                if let ScExpr::Ident(sym) = &exp.expr
                    && !sym.is_place()
                {
                    self.sink.emit(BorrowMutWhenNotDefinedMut {
                        loc_def: sym.loc().unwrap(),
                        name_def: sym.name(),
                        loc: expr.loc.clone().unwrap(),
                    })
                }

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

                let mut args_ty: Vec<Type> = args_ty.clone();

                if args_ty.len() != args.len() {
                    // arity doesn't match
                    self.sink.emit(ArityDoesntMatch {
                        expected: args_ty.len(),
                        got: args.len(),
                        loc: callee.loc.clone().unwrap(),
                    });

                    if args_ty.len() < args.len() {
                        let missing = args.len() - args_ty.len();
                        dbg!(missing);

                        args_ty.extend(iter::repeat_n(Type::Void, missing));
                    }
                }

                for (arg, aty) in zip(args, args_ty) {
                    self.ck_expr(arg, Some(aty.clone()))?;

                    self.expr_typeck(&aty, arg, None, None);
                }

                expr.typ = (**ret_ty).clone();
            }
            ScExpr::If {
                cond,
                then_br,
                else_br,
            } => {
                self.ck_expr(cond, Some(Type::Bool))?;

                self.expr_typeck(&Type::Bool, cond, None, None);

                self.ck_expr(then_br, coerce_to)?;

                if let Some(else_br) = else_br {
                    self.ck_expr(else_br, Some(then_br.typ.clone()))?;

                    self.expr_typeck(&then_br.typ, else_br, None, None);

                    expr.typ = then_br.typ.clone();
                } else {
                    expr.typ = Type::Void;
                }
            }
            ScExpr::Block {
                label,
                block,
                index,
            } => {
                if label.is_some() {
                    *index = Some(
                        self.label_stack
                            .define_label(label.clone(), LabelKind::Block),
                    );
                }

                self.ck_block(block, coerce_to)?;

                if let Some(index) = index
                    && let Some(info) = self.label_stack.get_by_idx(*index)
                    && !info.break_out
                {
                    let Some((label, loc)) = info.name.clone() else {
                        // SAFETY: cannot be reached because we only define a
                        // label info if there is a named label.
                        opt_unreachable!()
                    };

                    self.sink.emit(WUnusedLabel { loc, label })
                }

                expr.typ = if let Some(index) = index
                    && let Some(LabelInfo { typ, .. }) = self.label_stack.get_by_idx(*index)
                {
                    typ.clone().as_option().unwrap_or(block.typ.clone())
                } else {
                    block.typ.clone()
                };
            }
            ScExpr::Loop { label, body, index } => {
                // define label info

                // NOTE: here we are seeing if it is a predicate loop before
                // checking the code but i see no reason why it should not work.
                let is_predicate_loop = matches!(
                    body.stmts.first(),
                    Some(ScStatement {
                        stmt: ScStmt::Expression(ScExpression {
                            expr: ScExpr::If { .. },
                            typ: _,
                            loc: None
                        }),
                        loc: None
                    })
                );

                let kind = if is_predicate_loop {
                    LabelKind::PredicateLoop
                } else {
                    LabelKind::InfiniteLoop
                };

                *index = Some(self.label_stack.define_label(label.clone(), kind));

                // check the body
                self.ck_block(body, None)?;

                self.block_typeck(&Type::Void, body, None, None, None);

                let info = self
                    .label_stack
                    .get_by_idx(index.unwrap())
                    .expect("set the index just above");

                let break_out = info.break_out;

                expr.typ = if !break_out {
                    Type::Noreturn
                } else if info.typ != Type::Unknown {
                    info.typ.clone()
                } else {
                    Type::Void
                };
            }
            ScExpr::Return { expr: exp } => {
                if let Some(exp) = exp {
                    self.ck_expr(exp, Some(self.fun_retty.clone()))?;

                    self.expr_typeck(
                        &self.fun_retty.clone(),
                        exp,
                        self.fun_retty_loc.clone(),
                        None,
                    );
                } else if self.fun_retty != Type::Void {
                    // NOTE: we cannot use 'expr_typeck' here
                    self.sink.emit(MismatchedTypes {
                        expected: vec![self.fun_retty.clone()],
                        found: Type::Void,
                        due_to: self.fun_retty_loc.clone(),
                        notes: vec![],
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
                let (typ, kind) = if let Some(label) = label {
                    let Some(LabelInfo {
                        index: idx,
                        typ,
                        kind,
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

                    (typ.clone(), kind.clone())
                } else {
                    let Some(LabelInfo {
                        index: idx,
                        typ,
                        kind,
                        ..
                    }) = self.label_stack.last()
                    else {
                        return Err(LabelKwOutsideLoopOrBlock {
                            kw: "break",
                            loc: expr.loc.clone().unwrap(),
                        }
                        .into_diag());
                    };

                    if !kind.is_loop() {
                        return Err(BreakUseAnImplicitLabelInBlock {
                            loc: expr.loc.clone().unwrap(),
                        }
                        .into_diag());
                    }

                    *index = Some(*idx);

                    (typ.clone(), kind.clone())
                };

                // we indicate that we used this label inside a break.
                self.label_stack.set_breaked_out(index.unwrap());

                if let Some(exp) = exp {
                    self.ck_expr(exp, None)?;

                    if !kind.can_have_val() {
                        self.sink.emit(BreakWithValueUnsupported {
                            loc: expr.loc.clone().unwrap(),
                        })
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

                        self.expr_typeck(&info.typ.clone(), exp, None, None);
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

                    // NOTE: we cannot use 'expr_typeck' here
                    self.sink.emit(MismatchedTypes {
                        expected: vec![info.typ.clone()],
                        found: Type::Void,
                        due_to: None,
                        notes: vec![],
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
                            index: idx, kind, ..
                        }) = self.label_stack.get_by_name(&label)
                        else {
                            self.sink.emit(UseOfUndefinedLabel {
                                name: label.clone(),
                                // TODO: add location of the label name
                                loc: expr.loc.clone().unwrap(),
                            });

                            break 'blk;
                        };

                        if !kind.is_loop() {
                            self.sink.emit(CantContinueABlock {
                                loc: expr.loc.clone().unwrap(),
                            });

                            break 'blk;
                        }

                        *index = Some(*idx);
                    } else {
                        let Some(LabelInfo {
                            index: idx, kind, ..
                        }) = self.label_stack.last()
                        else {
                            self.sink.emit(LabelKwOutsideLoopOrBlock {
                                kw: "continue",
                                loc: expr.loc.clone().unwrap(),
                            });

                            break 'blk;
                        };

                        if !kind.is_loop() {
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
                    feature: "optional types",
                    label: "'null' represent not having a value",
                    loc: expr.loc.clone().unwrap()
                });

                expr.typ = Type::Void;
            }
            ScExpr::MemberAccess { expr: _, member: _ } => {
                self.sink.emit(feature_todo! {
                    feature: "field access",
                    label: "field access and struct type definition",
                    loc: expr.loc.clone().unwrap()
                });

                expr.typ = Type::Void;
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
            ScExpr::Poisoned { diag } => {
                self.sink.emit(diag.take().unwrap());

                // NOTE: set a dummy type to hopefully reduce the amount of
                // unnecessary diags
                expr.typ = Type::Void;
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
        if let Some(expr) = &mut block.last_expr {
            self.ck_expr(expr, coerce_to)?;
        }

        // compute if one of the statements or the last expression has
        // `noreturn` type.
        let is_noreturn = block
            .stmts
            .iter()
            .position(|stmt| match &stmt.stmt {
                ScStmt::VariableDef { value, .. } if value.typ == Type::Noreturn => true,
                ScStmt::Expression(expr) if expr.typ == Type::Noreturn => true,
                _ => false,
            })
            .map(|pos| NoreturnPos::Statements { pos })
            .map(|noret_pos| match block.last_expr.as_ref() {
                Some(expr) if expr.typ == Type::Unknown => NoreturnPos::LastExpr,
                _ => noret_pos,
            });

        block.typ = if let Some(noret_pos) = is_noreturn {
            if let NoreturnPos::Statements { pos } = noret_pos
                && pos + 1 < block.stmts.len()
            {
                let noret_loc = block.stmts.get(pos).unwrap().loc.clone().unwrap();
                let loc = block.stmts.get(pos + 1).unwrap().loc.clone().unwrap();

                self.sink.emit(WUnreachableCode { noret_loc, loc });
            } else if let NoreturnPos::Statements { pos } = noret_pos
                && let Some(last) = &block.last_expr
                && let Some(noret_loc) = block.stmts.get(pos).unwrap().loc.clone()
            {
                let loc = last.loc.clone().unwrap();

                self.sink.emit(WUnreachableCode { noret_loc, loc });
            }

            Type::Noreturn
        } else if let Some(expr) = &mut block.last_expr {
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
                    let value = self.evaluate_expr(typexpr).map_err(|(loc, note)| {
                        CantResolveComptimeValue {
                            note,
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
                } else if let Some(typ) = &typexpr_as_type {
                    self.expr_typeck(typ, value, typexpr.as_ref().unwrap().loc.clone(), None);
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
