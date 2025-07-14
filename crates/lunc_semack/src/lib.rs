use std::collections::HashMap;
use std::fmt::{Debug, Display};
use std::iter::zip;
use std::ops::Deref;
use std::sync::{Arc, RwLock};

use ckast::{
    CkArg, CkBlock, CkExpr, CkExpression, CkProgram, CkStatement, CkStmt, FromAst, MaybeUnresolved,
};
use diags::{
    ExpectedTypeFoundExpr, LoopKwOutsideLoop, MismatchedTypes, MutationOfImmutable,
    NameDefinedMultipleTimes, NeverUsedSymbol, NotFoundInScope, TypeAnnotationsNeeded,
    UnderscoreInExpression, UnderscoreReservedIdent, UnknownType,
};
use lunc_diag::{Diagnostic, DiagnosticSink, ToDiagnostic, feature_todo};
use lunc_parser::expr::{BinOp, UnaryOp};
use lunc_parser::item::Program;
pub use lunc_parser::item::Vis;
use lunc_utils::Span;

pub mod ckast;
pub mod diags;

/// Semantic checker, ensure all of the lun's semantic is correct, it also
/// include type checking.
#[derive(Debug, Clone)]
pub struct SemanticCk {
    /// program to check
    program: Program,
    /// diagnostic sink, used to emit diagnostics
    sink: DiagnosticSink,
    /// symbol table of the program
    table: SymbolTable,
    /// the return type of the current function
    fun_retaty: AtomicType,
    /// location of the return type (if defined) of the current function
    fun_retaty_loc: Option<Span>,
    /// loop stack used to check the type of loops and break values
    loop_stack: LoopStack,
}

pub trait TypeExpectation {
    fn matches(&self, other: &AtomicType) -> bool;

    fn as_string(&self) -> String;

    fn can_coerce(&self, other: &AtomicType) -> Option<AtomicType> {
        _ = other;

        None
    }

    fn dbg(&self);
}

impl TypeExpectation for AtomicType {
    fn matches(&self, other: &AtomicType) -> bool {
        self == other
    }

    fn as_string(&self) -> String {
        self.to_string()
    }

    fn dbg(&self) {
        println!("{self:?}");
    }
}

impl<S: ToString, F: Fn(&AtomicType) -> bool> TypeExpectation for (S, F) {
    fn matches(&self, other: &AtomicType) -> bool {
        self.1(other)
    }

    fn as_string(&self) -> String {
        self.0.to_string()
    }

    fn dbg(&self) {
        println!("({:?}, *expectation_check_function*)", self.0.to_string());
    }
}

impl<T: TypeExpectation> TypeExpectation for &T {
    fn matches(&self, other: &AtomicType) -> bool {
        T::matches(self, other)
    }

    fn as_string(&self) -> String {
        T::as_string(self)
    }

    fn can_coerce(&self, other: &AtomicType) -> Option<AtomicType> {
        T::can_coerce(self, other)
    }

    fn dbg(&self) {
        T::dbg(self);
    }
}

pub trait ExprAtomicType {
    fn atomic_type(&self) -> &AtomicType;

    fn set_atomic_type(&mut self, new: AtomicType);
}

impl ExprAtomicType for CkBlock {
    fn atomic_type(&self) -> &AtomicType {
        &self.atomtyp
    }

    fn set_atomic_type(&mut self, new: AtomicType) {
        self.atomtyp = new;
    }
}

impl ExprAtomicType for CkExpression {
    fn atomic_type(&self) -> &AtomicType {
        &self.atomtyp
    }

    fn set_atomic_type(&mut self, new: AtomicType) {
        self.atomtyp = new;
    }
}

impl<T: ExprAtomicType> ExprAtomicType for Box<T> {
    fn atomic_type(&self) -> &AtomicType {
        T::atomic_type(self.as_ref())
    }

    fn set_atomic_type(&mut self, new: AtomicType) {
        T::set_atomic_type(self.as_mut(), new);
    }
}

impl SemanticCk {
    pub fn new(ast: Program, sink: DiagnosticSink) -> SemanticCk {
        SemanticCk {
            program: ast,
            sink,
            table: SymbolTable::new(),
            fun_retaty: AtomicType::Unknown,
            fun_retaty_loc: None,
            loop_stack: LoopStack::new(),
        }
    }

    pub fn produce(&mut self) -> Option<CkProgram> {
        // 1. create the checked program from the unchecked program.
        let mut ckprogram = CkProgram::from_ast(self.program.clone());

        // 2. check all the defs and everything following will be checked
        match self.check_program(&mut ckprogram) {
            Ok(()) => {}
            Err(e) => {
                self.sink.push(e);
                return Some(ckprogram);
            }
        }

        Some(ckprogram)
    }

    pub fn type_check(
        &mut self,
        expectation: impl TypeExpectation,
        expr: &mut dyn ExprAtomicType,
        due_to: impl Into<Option<Span>>,
        loc: impl Into<Span>,
    ) {
        let aty = expr.atomic_type().clone();

        if !expectation.matches(&aty) {
            if let Some(new_aty) = expectation.can_coerce(&aty) {
                expr.set_atomic_type(new_aty);
                return;
            }

            self.sink.push(MismatchedTypes {
                expected: expectation.as_string(),
                found: aty.clone(),
                due_to: due_to.into(),
                loc: loc.into(),
            });
        }
    }

    pub fn check_program(&mut self, ckprogram: &mut CkProgram) -> Result<(), Diagnostic> {
        // 1. pre bind definitions

        self.table.scope_enter(); // program scope

        for def in &mut ckprogram.defs {
            let CkExpr::FunDefinition {
                args,
                rettype,
                body: _,
            } = &mut def.value.expr
            else {
                self.sink.push(feature_todo! {
                    feature: "global variables",
                    label: "global aren't yet supported, only functions in definitions",
                    loc: def.loc.clone()
                });
                continue;
            };

            let mut args_atomtype = Vec::new();
            for CkArg { typ, .. } in args {
                self.check_expr(typ, Some(AtomicType::Type))?;

                if typ.atomtyp != AtomicType::Type {
                    self.sink.push(ExpectedTypeFoundExpr {
                        help: false,
                        loc: typ.loc.clone(),
                    });
                }

                if let Some(atomtyp) = AtomicType::from_expr(typ.clone()) {
                    args_atomtype.push(atomtyp);
                } else {
                    self.sink.push(UnknownType {
                        typ: typ.to_string(),
                        loc: typ.loc.clone(),
                    });

                    // poisoned value
                    args_atomtype.push(AtomicType::Void);
                };
            }

            let ret_aty = if let Some(typ) = rettype {
                self.check_expr(typ, Some(AtomicType::Type))?;

                if let Some(atomtyp) = AtomicType::from_expr((**typ).clone()) {
                    Box::new(atomtyp)
                } else {
                    self.sink.push(UnknownType {
                        typ: typ.to_string(),
                        loc: typ.loc.clone(),
                    });

                    // poisoned value
                    Box::new(AtomicType::Void)
                }
            } else {
                Box::new(AtomicType::Void)
            };

            let mut ckname = def.name.clone();
            if ckname == "_" {
                self.sink.push(UnderscoreReservedIdent {
                    loc: def.name_loc.clone(),
                });
                ckname = String::from("\0");
            }

            let symbol = SymbolRef::new(Symbol::function(
                AtomicType::Fun {
                    args: args_atomtype,
                    ret: ret_aty,
                },
                ckname.clone(),
                self.table.global_count(),
                // TODO: add a new loc that points to the signature
                def.loc.clone(),
                def.vis.clone(),
            ));
            def.sym = MaybeUnresolved::Resolved(symbol.clone());

            self.table.bind(ckname, symbol)?;
        }

        // 2. now, check the rest of the program

        for def in &mut ckprogram.defs {
            let CkExpr::FunDefinition {
                args,
                rettype,
                body,
            } = &mut def.value.expr
            else {
                self.sink.push(feature_todo! {
                    feature: "global variables",
                    label: "global aren't yet supported, only functions in definitions",
                    loc: def.loc.clone()
                });
                continue;
            };

            // reset the loop stack for this new function
            self.loop_stack.reset();

            // yeah this is kinda ugly code but.. it works
            let fun_ret_atyp = def.sym.unwrap().read().unwrap().atomtyp.as_fun_ret();

            // store return type to check `return` expr after.
            self.fun_retaty = fun_ret_atyp.clone();
            self.fun_retaty_loc = rettype.as_ref().map(|e| e.loc.clone());

            self.table.scope_enter(); // function scope

            // put the arguments in the symbol table
            for CkArg {
                name,
                name_loc,
                typ,
                loc: _,
            } in args
            {
                let Some(ty) = AtomicType::from_expr(typ.clone()) else {
                    return Err(UnknownType {
                        typ: typ.to_string(),
                        loc: typ.loc.clone(),
                    }
                    .into_diag());
                };

                let mut ckname = name.clone();
                if name == "_" {
                    self.sink.push(UnderscoreReservedIdent {
                        loc: name_loc.clone(),
                    });
                    ckname = String::from("\0");
                }

                self.table.bind(
                    ckname.clone(),
                    SymbolRef::new(Symbol::arg(
                        ty,
                        ckname.clone(),
                        self.table.arg_count(),
                        name_loc.clone(),
                    )),
                )?;
            }

            self.check_block(body, Some(fun_ret_atyp.clone()))?;

            // here we don't use self.type_check(..) because we don't want to
            // coerce to any type
            if body.atomtyp != fun_ret_atyp {
                self.sink.push(MismatchedTypes {
                    expected: fun_ret_atyp.to_string(),
                    found: body.atomtyp.clone(),
                    due_to: rettype.as_ref().map(|e| e.loc.clone()),
                    loc: body.loc.clone(),
                });
            }

            self.table.scope_exit(&mut self.sink); // function scope
        }

        self.table.scope_exit(&mut self.sink); // program scope

        Ok(())
    }

    pub fn check_block(
        &mut self,
        block: &mut CkBlock,
        wish: Option<AtomicType>,
    ) -> Result<(), Diagnostic> {
        // 1. check all the stmts
        for stmt in &mut block.stmts {
            match self.check_stmt(stmt) {
                Ok(()) => {}
                Err(d) => self.sink.push(d),
            }
        }

        // 2. check the last_expr if any
        if let Some(expr) = &mut block.last_expr {
            self.check_expr(expr, wish)?;
            block.atomtyp = expr.atomtyp.clone();
        } else {
            block.atomtyp = AtomicType::Void;
        }

        Ok(())
    }

    pub fn check_stmt(&mut self, stmt: &mut CkStatement) -> Result<(), Diagnostic> {
        match &mut stmt.stmt {
            CkStmt::VariableDef {
                name,
                name_loc,
                mutable,
                typ,
                value,
                sym,
            } => {
                // check the type
                if let Some(ty) = typ {
                    self.check_expr(ty, Some(AtomicType::Type))?;

                    if ty.atomtyp != AtomicType::Type {
                        self.sink.push(
                            ExpectedTypeFoundExpr {
                                help: false,
                                loc: ty.loc.clone(),
                            }
                            .into_diag(),
                        );
                    }
                }

                let type_as_atomic = if let Some(ty) = typ {
                    let Some(atomtyp) = AtomicType::from_expr(ty.clone()) else {
                        return Err(UnknownType {
                            typ: ty.to_string(),
                            loc: ty.loc.clone(),
                        }
                        .into_diag());
                    };
                    Some(atomtyp)
                } else {
                    None
                };

                // check the value
                self.check_expr(value, type_as_atomic.clone())?;

                if let Some(ref typ_as_aty) = type_as_atomic {
                    let value_loc = value.loc.clone();

                    self.type_check(
                        typ_as_aty,
                        value,
                        typ.as_ref().map(|e| e.loc.clone()),
                        value_loc,
                    );
                }

                let atomtyp = if let Some(ref typ_as_aty) = type_as_atomic {
                    typ_as_aty.clone()
                } else {
                    value.atomtyp.clone()
                };

                let mut ckname = name.clone();
                if name == "_" {
                    self.sink.push(UnderscoreReservedIdent {
                        loc: name_loc.clone(),
                    });
                    ckname = String::from("\0");
                }

                let symbol = SymbolRef::new(Symbol::var(
                    atomtyp,
                    ckname.clone(),
                    self.table.var_count(),
                    stmt.loc.clone(),
                    *mutable,
                ));

                *sym = MaybeUnresolved::Resolved(symbol.clone());
                self.table.bind(ckname, symbol)?;
            }
            CkStmt::Expression(expr) => {
                self.check_expr(expr, None)?;
            }
        }
        Ok(())
    }

    /// check an expression and mutate it in place if needed, you can optionally
    /// provide the type expected for this expression.
    ///
    /// eg: a variable with a type attached to it expect its value to be of some
    /// type, a function call expects it to be of some type, etc, etc
    ///
    /// IMPORTANT: note that the "expected" type is just a suggestion, if the
    /// type of the expr is UnkConstrained it will try to coerce to the expected
    /// type but if the type is not a constrain it will do nothing, it's just a
    /// suggestion
    pub fn check_expr(
        &mut self,
        expr: &mut CkExpression,
        mut wish: Option<AtomicType>,
    ) -> Result<(), Diagnostic> {
        // remove the wish if it's to be unknown
        if let Some(AtomicType::Unknown) = wish {
            wish = None;
        }

        match &mut expr.expr {
            CkExpr::IntLit(_) => {
                expr.atomtyp = AtomicType::UnkConstrained(Constraint::Integer);
            }
            CkExpr::BoolLit(_) => {
                expr.atomtyp = AtomicType::Bool;
            }
            CkExpr::StringLit(_) => {
                expr.atomtyp = AtomicType::Str;
            }
            CkExpr::Grouping(e) => {
                self.check_expr(e, wish.clone())?;
                expr.atomtyp = e.atomtyp.clone();
            }
            CkExpr::Ident(MaybeUnresolved::Unresolved(name)) => {
                let Some(symref) = self.table.lookup(&*name, true) else {
                    return Err(NotFoundInScope {
                        name: name.clone(),
                        loc: expr.loc.clone(),
                    }
                    .into_diag());
                };
                let sym = symref.read().unwrap();

                if sym.name == "_" {
                    return Err(UnderscoreInExpression {
                        loc: expr.loc.clone(),
                    }
                    .into_diag());
                }
                if sym.atomtyp == AtomicType::Unknown {
                    self.sink.push(TypeAnnotationsNeeded {
                        loc: sym.loc.clone(),
                    })
                }
                expr.atomtyp = sym.atomtyp.clone();
                expr.expr = CkExpr::Ident(MaybeUnresolved::Resolved(symref.clone()));
            }
            CkExpr::Ident(MaybeUnresolved::Resolved(_)) => {
                unreachable!("i think it's a bug not sure tho")
            }
            // special case of assignment to _
            //
            // it is used to allow
            // _ = expr;
            //
            // where expr is evaluated, and its return value is ignored, _
            // coerce to any type.
            CkExpr::Binary {
                lhs,
                op: BinOp::Assignment,
                rhs,
            } if matches!(
                &lhs.expr,
                CkExpr::Ident(MaybeUnresolved::Unresolved(id)) if id.as_str() == "_"
            ) =>
            {
                // manually checking lhs
                let Some(symref) = self.table.lookup("_", true) else {
                    unreachable!();
                };
                let sym = symref.read().unwrap();

                assert_eq!(sym.atomtyp, AtomicType::Unknown);
                lhs.expr = CkExpr::Ident(MaybeUnresolved::Resolved(symref.clone()));

                self.check_expr(rhs, None)?;

                expr.atomtyp = AtomicType::Void;
            }
            // other special case of Binary, make assignment evaluate to Void
            CkExpr::Binary {
                lhs,
                op: BinOp::Assignment,
                rhs,
            } => {
                self.check_expr(lhs, wish.clone())?;
                self.check_expr(rhs, Some(lhs.atomtyp.clone()))?;

                let rhs_loc = rhs.loc.clone();
                self.type_check(&lhs.atomtyp, &mut **rhs, None, rhs_loc);

                expr.atomtyp = AtomicType::Void;

                // check that if lhs is a variable, the variable is mutable
                // TODO: check if pointer is mutable also

                if let CkExpr::Ident(MaybeUnresolved::Resolved(symref)) = &lhs.expr {
                    let sym = symref.read().unwrap();

                    if let Symbol {
                        kind: SymKind::Var { mutable: false },
                        name,
                        loc,
                        ..
                    } = sym.clone()
                    {
                        self.sink.push(MutationOfImmutable {
                            var_name: name.clone(),
                            var_loc: loc.clone(),
                            loc: expr.loc.clone(),
                        });
                    }
                }
            }
            CkExpr::Binary { lhs, op, rhs } => {
                self.check_expr(lhs, wish.clone())?;
                self.check_expr(rhs, wish.clone())?;

                let rhs_loc = rhs.loc.clone();

                if let AtomicType::UnkConstrained(constraint) = &lhs.atomtyp {
                    // lhs is unknown constrained, we need to check that the
                    // constraint and the rhs type kinda match
                    let coercible_types = match constraint {
                        Constraint::Integer => Constraint::INTEGER_COERCIBLE_TYPES,
                        Constraint::Float => Constraint::FLOAT_COERCIBLE_TYPES,
                    };

                    if !coercible_types.contains(&rhs.atomtyp) {
                        // we not fine
                        self.sink.push(MismatchedTypes {
                            expected: lhs.atomtyp.to_string(),
                            found: rhs.atomtyp.clone(),
                            due_to: None,
                            loc: rhs.loc.clone(),
                        });
                    }
                } else {
                    self.type_check(&lhs.atomtyp, &mut **rhs, None, rhs_loc);
                }

                expr.atomtyp = if op.is_relational() | op.is_logical() {
                    AtomicType::Bool
                } else if let AtomicType::UnkConstrained(_) = lhs.atomtyp {
                    rhs.atomtyp.clone()
                } else {
                    lhs.atomtyp.clone()
                };
            }
            CkExpr::Unary { op, val } => {
                match op {
                    UnaryOp::Negation => {
                        self.check_expr(val, wish.clone())?;

                        let exp_loc = val.loc.clone();

                        self.type_check(
                            ("integer or float", |other: &AtomicType| {
                                other.is_integer() || other.is_float()
                            }),
                            &mut **val,
                            None,
                            exp_loc,
                        );
                        expr.atomtyp = val.atomtyp.clone();
                    }
                    UnaryOp::Not => {
                        self.check_expr(val, wish.clone())?;
                        let exp_loc = val.loc.clone();

                        self.type_check(AtomicType::Bool, &mut **val, None, exp_loc);
                        expr.atomtyp = AtomicType::Bool;
                    }
                    UnaryOp::Dereference => {
                        let real_wish = if let Some(AtomicType::Pointer {
                            mutable: _,
                            pointed,
                        }) = &wish
                        {
                            Some((**pointed).clone())
                        } else {
                            None
                        };
                        self.check_expr(val, real_wish)?;

                        let pointee = if let AtomicType::Pointer {
                            mutable: _,
                            ref pointed,
                        } = val.atomtyp
                        {
                            // we fine bro :)
                            (**pointed).clone()
                        } else {
                            return Err(MismatchedTypes {
                                expected: String::from("pointer"),
                                found: val.atomtyp.clone(),
                                due_to: None,
                                loc: val.loc.clone(),
                            }
                            .into_diag()
                            .with_note(format!("type `{}` cannot dereferenced", val.atomtyp)));
                        };

                        expr.atomtyp = pointee;
                    }
                }
            }
            CkExpr::FunCall { called, args } => {
                // TODO: constrain the `called` value to a function pointer,
                // replace wish Option<AtomicType> to Option<AtyWish>
                self.check_expr(called, None)?;

                let AtomicType::Fun {
                    args: args_aty,
                    ret: ret_ty,
                } = &called.atomtyp
                else {
                    return Err(MismatchedTypes {
                        expected: "function".to_string(),
                        found: called.atomtyp.clone(),
                        due_to: None,
                        loc: called.loc.clone(),
                    }
                    .into_diag());
                };

                assert!(called.atomtyp.is_func());

                for (arg, aty) in zip(args, args_aty) {
                    self.check_expr(arg, Some(aty.clone()))?;

                    let val_loc = arg.loc.clone();
                    self.type_check(aty, arg, None, val_loc);
                }

                expr.atomtyp = *ret_ty.clone();
            }
            CkExpr::FunDefinition { .. } => {
                return Err(feature_todo! {
                    feature: "function closure",
                    label: "closures are not yet supported, you can only define functions",
                    loc: expr.loc.clone()
                }
                .into_diag());
            }
            CkExpr::If {
                cond,
                then_branch,
                else_branch,
            } => {
                // 1. condition
                self.check_expr(cond, Some(AtomicType::Bool))?;

                let cond_loc = cond.loc.clone();
                self.type_check(AtomicType::Bool, &mut **cond, None, cond_loc);

                // 2. then branch
                self.check_expr(then_branch, None)?;

                // 3. set the atomtyp to the type of then_branch
                expr.atomtyp = then_branch.atomtyp.clone();

                // 4. else branch
                if let Some(else_branch) = else_branch {
                    self.check_expr(else_branch, Some(then_branch.atomtyp.clone()))?;

                    let else_branch_loc = else_branch.loc.clone();

                    self.type_check(
                        expr.atomtyp.clone(),
                        &mut **else_branch,
                        None,
                        else_branch_loc,
                    );
                }
            }
            CkExpr::Block(block) => {
                self.check_block(block, wish.clone())?;
                expr.atomtyp = block.atomtyp.clone();
            }
            CkExpr::While { cond, body, index } => {
                // 1. condition
                self.check_expr(cond, Some(AtomicType::Bool))?;

                let cond_loc = cond.loc.clone();
                self.type_check(AtomicType::Bool, &mut **cond, None, cond_loc);

                // 2. allocate loop index
                *index = Some(self.loop_stack.alloc_loop());

                // 3. body
                self.check_block(body, None)?;

                expr.atomtyp =
                    if let Some(Loop { atomtyp, .. }) = self.loop_stack.get(index.unwrap()) {
                        atomtyp.clone().replace(AtomicType::Void)
                    } else {
                        AtomicType::Void
                    };
            }
            CkExpr::For { .. } => {
                // TODO: implement for loops

                self.sink.push(feature_todo! {
                    feature: "for loop",
                    label: "iterators are not implemented so..",
                    loc: expr.loc.clone(),
                });

                expr.atomtyp = AtomicType::Void;
            }
            CkExpr::Return { val } => {
                expr.atomtyp = AtomicType::Noreturn;

                if let Some(val) = val {
                    self.check_expr(val, Some(self.fun_retaty.clone()))?;

                    let val_loc = val.loc.clone();

                    self.type_check(
                        self.fun_retaty.clone(),
                        &mut **val,
                        self.fun_retaty_loc.clone(),
                        val_loc,
                    );
                }
            }
            CkExpr::Break { val, index } => {
                expr.atomtyp = AtomicType::Noreturn;

                // 1. assign loop index
                let Some(Loop {
                    index: new_idx,
                    atomtyp,
                }) = self.loop_stack.last().cloned()
                else {
                    return Err(LoopKwOutsideLoop {
                        kw: "break",
                        loc: expr.loc.clone(),
                    }
                    .into_diag());
                };

                *index = Some(new_idx);
                let idx = index.unwrap();

                // 2. check the value
                if let Some(val) = val {
                    self.check_expr(val, Some(atomtyp.clone()))?;

                    if atomtyp == AtomicType::Unknown {
                        self.loop_stack.set_atomtyp(idx, val.atomtyp.clone());
                    } else {
                        let val_loc = val.loc.clone();

                        self.type_check(atomtyp, &mut **val, None, val_loc);
                    };
                } else if atomtyp == AtomicType::Unknown {
                    self.loop_stack.set_atomtyp(idx, AtomicType::Void);
                } else {
                    self.sink.push(
                        MismatchedTypes {
                            expected: atomtyp.as_string(),
                            found: AtomicType::Void,
                            due_to: None,
                            loc: expr.loc.clone(),
                        }
                        .into_diag()
                        .with_note("help: give the `break` a value of the expected type"),
                    );
                }
            }
            CkExpr::Continue { index } => {
                expr.atomtyp = AtomicType::Noreturn;

                // assign loop index
                let Some(Loop { index: new_idx, .. }) = self.loop_stack.last().cloned() else {
                    return Err(LoopKwOutsideLoop {
                        kw: "continue",
                        loc: expr.loc.clone(),
                    }
                    .into_diag());
                };
                *index = Some(new_idx);
            }
            CkExpr::Null => {
                // TODO: make it coerce to pointer also
                expr.atomtyp = AtomicType::Void;
            }
            CkExpr::PointerType { typ, .. } => {
                self.check_expr(typ, Some(AtomicType::Type))?;

                if typ.atomtyp != AtomicType::Type {
                    self.sink.push(UnknownType {
                        typ: typ.to_string(),
                        loc: typ.loc.clone(),
                    })
                }

                expr.atomtyp = AtomicType::Type;
            }
            CkExpr::Deref { mutable, val } => {
                // TODO: if we expected a pointer to be mutable / immutable
                // and the value was a deref, add an help message like "try to
                // remove / add the `mut` keyword"
                // TODO: be able to wish a pointer (mutable / immutable)
                self.check_expr(val, None)?;

                expr.atomtyp = AtomicType::Pointer {
                    mutable: *mutable,
                    pointed: Box::new(val.atomtyp.clone()),
                };
            }
        }

        if let AtomicType::UnkConstrained(constraint) = &expr.atomtyp {
            if let Some(new_atomtyp) = constraint.can_fulfill_wish(&wish) {
                self.apply_expression_wish(expr, new_atomtyp);
            } else {
                // here we are doing nothing if the wish is not fulfilled because later down the line a diag will be emitted
            }
        }

        debug_assert_ne!(expr.atomtyp, AtomicType::Unknown);
        Ok(())
    }

    pub fn apply_expression_wish(&self, expr: &mut CkExpression, new_aty: AtomicType) {
        if let CkExpr::Ident(MaybeUnresolved::Resolved(symref)) = &mut expr.expr {
            let mut sym = symref.write().unwrap();
            sym.atomtyp = new_aty.clone();
            // TODO: modify everywhere the symbol to be with the new type
        }
        expr.atomtyp = new_aty;
    }
}

/// A reference to a symbol, used to mutate symbols everywhere, in the SymbolTable and in the Checked ast.
#[repr(transparent)]
#[derive(Debug, Clone)]
pub struct SymbolRef(Arc<RwLock<Symbol>>);

impl SymbolRef {
    pub fn new(symbol: Symbol) -> SymbolRef {
        SymbolRef(Arc::new(RwLock::new(symbol)))
    }
}

impl Deref for SymbolRef {
    type Target = Arc<RwLock<Symbol>>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

/// Symbol
#[derive(Debug, Clone)]
pub struct Symbol {
    /// local, parameter or global
    pub kind: SymKind,
    /// actual type of the
    pub atomtyp: AtomicType,
    /// the name of the symbol
    ///
    /// For function (see kind):
    /// - the name is the unmangled symbol name of the function in the output assembly
    pub name: String,
    /// which scope the symbol is referring to
    pub which: usize,
    /// location of the definition of the symbol, must point to at least the
    /// identifier and can point to more: the identifier and the type ...
    pub loc: Span,
    /// count of how many times this symbol is used
    pub uses: usize,
    /// Visilibity of a symbol, for variables and argument it's always private,
    /// for global and function it can be public or private
    pub vis: Vis,
}

impl Symbol {
    /// Create a new symbol
    pub fn new(
        kind: SymKind,
        atomtyp: AtomicType,
        name: String,
        which: usize,
        loc: Span,
        vis: Vis,
    ) -> Symbol {
        Symbol {
            kind,
            atomtyp,
            name,
            which,
            loc,
            uses: 0,
            vis,
        }
    }

    /// Create a new local symbol
    pub fn var(
        atomtyp: AtomicType,
        name: String,
        which: usize,
        loc: Span,
        mutable: bool,
    ) -> Symbol {
        Symbol {
            kind: SymKind::Var { mutable },
            atomtyp,
            name,
            which,
            loc,
            uses: 0,
            vis: Vis::Private,
        }
    }

    /// Create a new param symbol
    pub fn arg(atomtyp: AtomicType, name: String, which: usize, loc: Span) -> Symbol {
        Symbol {
            kind: SymKind::Arg,
            atomtyp,
            name,
            which,
            loc,
            uses: 0,
            vis: Vis::Private,
        }
    }

    /// Create a new global symbol
    pub fn global(atomtyp: AtomicType, name: String, which: usize, loc: Span, vis: Vis) -> Symbol {
        Symbol {
            kind: SymKind::Global,
            atomtyp,
            name,
            which,
            loc,
            uses: 0,
            vis,
        }
    }

    /// Create a new function symbol
    pub fn function(
        atomtyp: AtomicType,
        name: String,
        which: usize,
        loc: Span,
        vis: Vis,
    ) -> Symbol {
        Symbol {
            kind: SymKind::Function,
            atomtyp,
            name,
            which,
            loc,
            uses: 0,
            vis,
        }
    }

    pub fn kind(mut self, kind: SymKind) -> Symbol {
        self.kind = kind;
        self
    }

    pub fn atomtyp(mut self, atomtyp: AtomicType) -> Symbol {
        self.atomtyp = atomtyp;
        self
    }

    pub fn name(mut self, name: String) -> Symbol {
        self.name = name;
        self
    }

    pub fn which(mut self, which: usize) -> Symbol {
        self.which = which;
        self
    }
}

/// Symbol type
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SymKind {
    /// Variable
    Var { mutable: bool },
    /// Argument
    Arg,
    /// Global
    Global,
    /// Function
    Function,
}

impl Display for SymKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            SymKind::Var { .. } => f.write_str("variable"),
            SymKind::Arg => f.write_str("argument"),
            SymKind::Global => f.write_str("global"),
            SymKind::Function => f.write_str("function"),
        }
    }
}

/// An atomic type is the real underlying type of a Checked Expression,
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub enum AtomicType {
    /// Unknown, at the end of type checking this type is an error.
    #[default]
    Unknown,
    /// The type is unknown but we constrained it, we know some information on
    /// this type: it is an integer type, a float type etc..
    UnkConstrained(Constraint),
    /// 8 bit signed integer
    I8,
    /// 16 bit signed integer
    I16,
    /// 32 bit signed integer
    I32,
    /// 64 bit signed integer
    ///
    /// NOTE: the exprtype `int` is an alias of `i64` exprtype
    I64,
    /// Pointer-sized signed integer type
    Isize,
    /// 8 bit unsigned integer
    U8,
    /// 16 bit unsigned integer
    U16,
    /// 32 bit unsigned integer
    U32,
    /// 64 bit unsigned integer
    ///
    /// NOTE: the exprtype `uint` is an alias of `u64` exprtype
    U64,
    /// Pointer-sized unsigned integer type
    Usize,
    /// 32 bit floating point number, compliant with IEEE 754-2008
    F32,
    /// 16 bit floating point number, compliant with IEEE 754-2008
    F16,
    /// 64 bit floating point number, compliant with IEEE 754-2008
    F64,
    /// equivalent of Rust's `bool`, always one byte long. Can only contain
    /// `true` -> 1 and `false` -> 0
    Bool,
    // TODO: implement strings
    /// a string, nothing for now, we can't use them
    Str,
    /// void. nothing, default return type of a function without a return type.
    Void,
    /// a function type, can only be constructed from a function definition.
    Fun {
        /// types of the arguments
        args: Vec<AtomicType>,
        /// the return type
        ret: Box<AtomicType>,
    },
    /// Type, in the Type System.
    ///
    /// Because lun have types that are expression, types get typed checked as
    /// well. So (for example) the identifier `int` will be evaluated in EVERY
    /// expression to be of type `type`.
    Type,
    /// Noreturn, the type that return, break and continue expressions evaluate
    /// to.
    ///
    /// It indicates that the control flow will halts after evaluating the
    /// expression.
    Noreturn,
    /// pointer.
    Pointer {
        mutable: bool,
        pointed: Box<AtomicType>,
    },
}

impl AtomicType {
    pub const PRIMARY_ATOMTYPE_PAIRS: &[(&str, AtomicType)] = &[
        ("isize", AtomicType::Isize),
        ("i64", AtomicType::I64),
        ("i32", AtomicType::I32),
        ("i16", AtomicType::I16),
        ("i8", AtomicType::I8),
        ("usize", AtomicType::Usize),
        ("u64", AtomicType::U64),
        ("u32", AtomicType::U32),
        ("u16", AtomicType::U16),
        ("u8", AtomicType::U8),
        ("f16", AtomicType::F16),
        ("f32", AtomicType::F32),
        ("f64", AtomicType::F64),
        ("bool", AtomicType::Bool),
        ("str", AtomicType::Str),
        ("noreturn", AtomicType::Noreturn),
        ("void", AtomicType::Void),
    ];

    /// returns true if the type is a function
    pub const fn is_func(&self) -> bool {
        matches!(self, AtomicType::Fun { .. })
    }

    /// Converts a type expression to a type.
    pub fn from_expr(expr: CkExpression) -> Option<AtomicType> {
        match expr.expr {
            CkExpr::Ident(MaybeUnresolved::Resolved(symref)) => {
                let Symbol { name, .. } = symref.read().unwrap().clone();

                for (tyname, ty) in AtomicType::PRIMARY_ATOMTYPE_PAIRS {
                    if *tyname == name {
                        return Some(ty.clone());
                    }
                }

                None
            }
            CkExpr::PointerType { mutable, typ } => {
                // pointer type
                Some(AtomicType::Pointer {
                    mutable,
                    pointed: Box::new(AtomicType::from_expr(*typ)?),
                })
            }
            _ => None,
        }
    }

    /// Interpret the type as a Fun and return the return type
    #[track_caller]
    pub fn as_fun_ret(&self) -> AtomicType {
        match self {
            Self::Fun { ret, .. } => (**ret).clone(),
            _ => panic!("{self:?} is not a function type"),
        }
    }

    /// Interpret the type as a Fun and return the arguments types
    #[track_caller]
    pub fn as_fun_args(&self) -> Vec<AtomicType> {
        match self {
            Self::Fun { args, .. } => args.clone(),
            _ => panic!("{self:?} is not a function type"),
        }
    }

    /// Returns true if self is an integer type, so `iNN` or `uNN`
    pub fn is_integer(&self) -> bool {
        matches!(
            self,
            Self::I8
                | Self::I16
                | Self::I32
                | Self::I64
                | Self::U8
                | Self::U16
                | Self::U32
                | Self::U64
        )
    }

    /// Returns true if self is a float type, so `f16`, `f32` or `f64`
    pub fn is_float(&self) -> bool {
        matches!(self, Self::F16 | Self::F32 | Self::F64)
    }

    /// replace this type with `other` if `self` is unknown
    pub fn replace(mut self, other: AtomicType) -> AtomicType {
        if self == AtomicType::Unknown {
            self = other;
        }
        self
    }
}

impl Display for AtomicType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            AtomicType::Unknown => f.write_str("unknown"),
            AtomicType::UnkConstrained(constraint) => {
                write!(f, "<{constraint}>")
            }
            AtomicType::I64 => f.write_str("i64"),
            AtomicType::I32 => f.write_str("i32"),
            AtomicType::I16 => f.write_str("i16"),
            AtomicType::I8 => f.write_str("i8"),
            AtomicType::Isize => f.write_str("isize"),
            AtomicType::U64 => f.write_str("u64"),
            AtomicType::U32 => f.write_str("u32"),
            AtomicType::U16 => f.write_str("u16"),
            AtomicType::U8 => f.write_str("u8"),
            AtomicType::Usize => f.write_str("usize"),
            AtomicType::F16 => f.write_str("f16"),
            AtomicType::F32 => f.write_str("f32"),
            AtomicType::F64 => f.write_str("f64"),
            AtomicType::Bool => f.write_str("bool"),
            AtomicType::Str => f.write_str("str"),
            AtomicType::Void => f.write_str("void"),
            // TODO: implement a proper display for function type, like `fun(int, f16) -> bool`
            AtomicType::Fun { .. } => f.write_str("fun"),
            AtomicType::Type => f.write_str("type"),
            AtomicType::Noreturn => f.write_str("noreturn"),
            AtomicType::Pointer { mutable, pointed } => {
                f.write_str("*")?;
                if *mutable {
                    f.write_str("mut ")?;
                }
                Display::fmt(pointed, f)?;
                Ok(())
            }
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Constraint {
    Integer,
    Float,
}

impl Constraint {
    pub const INTEGER_COERCIBLE_TYPES: &[AtomicType] = &[
        AtomicType::Isize,
        AtomicType::I8,
        AtomicType::I16,
        AtomicType::I32,
        AtomicType::I64,
        AtomicType::Usize,
        AtomicType::U8,
        AtomicType::U16,
        AtomicType::U32,
        AtomicType::U64,
    ];

    pub const FLOAT_COERCIBLE_TYPES: &[AtomicType] =
        &[AtomicType::F16, AtomicType::F32, AtomicType::F64];

    pub fn can_fulfill_wish(&self, wish: &Option<AtomicType>) -> Option<AtomicType> {
        let wish = wish.as_ref()?;

        let coercible_types = match self {
            Self::Integer => Self::INTEGER_COERCIBLE_TYPES,
            Self::Float => Self::FLOAT_COERCIBLE_TYPES,
        };

        if coercible_types.contains(wish) {
            Some(wish.clone())
        } else {
            None
        }
    }
}

impl Display for Constraint {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Constraint::Integer => write!(f, "integer"),
            Constraint::Float => write!(f, "float"),
        }
    }
}

#[derive(Debug, Clone)]
pub struct SymbolMap {
    map: HashMap<String, SymbolRef>,
    function_count: usize,
    global_count: usize,
    var_count: usize,
    arg_count: usize,
}

impl SymbolMap {
    pub fn new() -> SymbolMap {
        SymbolMap {
            map: HashMap::new(),
            function_count: 0,
            global_count: 0,
            var_count: 0,
            arg_count: 0,
        }
    }

    pub fn first_scope() -> SymbolMap {
        SymbolMap {
            map: HashMap::from([
                (
                    "isize".to_string(),
                    SymbolRef::new(Symbol::global(
                        AtomicType::Type,
                        "isize".to_string(),
                        0,
                        Span::ZERO,
                        Vis::Public,
                    )),
                ),
                (
                    "i64".to_string(),
                    SymbolRef::new(Symbol::global(
                        AtomicType::Type,
                        "i64".to_string(),
                        0,
                        Span::ZERO,
                        Vis::Public,
                    )),
                ),
                (
                    "i32".to_string(),
                    SymbolRef::new(Symbol::global(
                        AtomicType::Type,
                        "i32".to_string(),
                        0,
                        Span::ZERO,
                        Vis::Public,
                    )),
                ),
                (
                    "i16".to_string(),
                    SymbolRef::new(Symbol::global(
                        AtomicType::Type,
                        "i16".to_string(),
                        0,
                        Span::ZERO,
                        Vis::Public,
                    )),
                ),
                (
                    "i8".to_string(),
                    SymbolRef::new(Symbol::global(
                        AtomicType::Type,
                        "i8".to_string(),
                        0,
                        Span::ZERO,
                        Vis::Public,
                    )),
                ),
                (
                    "usize".to_string(),
                    SymbolRef::new(Symbol::global(
                        AtomicType::Type,
                        "usize".to_string(),
                        0,
                        Span::ZERO,
                        Vis::Public,
                    )),
                ),
                (
                    "u64".to_string(),
                    SymbolRef::new(Symbol::global(
                        AtomicType::Type,
                        "u64".to_string(),
                        0,
                        Span::ZERO,
                        Vis::Public,
                    )),
                ),
                (
                    "u32".to_string(),
                    SymbolRef::new(Symbol::global(
                        AtomicType::Type,
                        "u32".to_string(),
                        0,
                        Span::ZERO,
                        Vis::Public,
                    )),
                ),
                (
                    "u16".to_string(),
                    SymbolRef::new(Symbol::global(
                        AtomicType::Type,
                        "u16".to_string(),
                        0,
                        Span::ZERO,
                        Vis::Public,
                    )),
                ),
                (
                    "u8".to_string(),
                    SymbolRef::new(Symbol::global(
                        AtomicType::Type,
                        "u8".to_string(),
                        0,
                        Span::ZERO,
                        Vis::Public,
                    )),
                ),
                (
                    "f16".to_string(),
                    SymbolRef::new(Symbol::global(
                        AtomicType::Type,
                        "f16".to_string(),
                        0,
                        Span::ZERO,
                        Vis::Public,
                    )),
                ),
                (
                    "f32".to_string(),
                    SymbolRef::new(Symbol::global(
                        AtomicType::Type,
                        "f32".to_string(),
                        0,
                        Span::ZERO,
                        Vis::Public,
                    )),
                ),
                (
                    "f64".to_string(),
                    SymbolRef::new(Symbol::global(
                        AtomicType::Type,
                        "f64".to_string(),
                        0,
                        Span::ZERO,
                        Vis::Public,
                    )),
                ),
                (
                    "bool".to_string(),
                    SymbolRef::new(Symbol::global(
                        AtomicType::Type,
                        "bool".to_string(),
                        0,
                        Span::ZERO,
                        Vis::Public,
                    )),
                ),
                (
                    "str".to_string(),
                    SymbolRef::new(Symbol::global(
                        AtomicType::Type,
                        "str".to_string(),
                        0,
                        Span::ZERO,
                        Vis::Public,
                    )),
                ),
                (
                    "noreturn".to_string(),
                    SymbolRef::new(Symbol::global(
                        AtomicType::Type,
                        "noreturn".to_string(),
                        0,
                        Span::ZERO,
                        Vis::Public,
                    )),
                ),
                (
                    "void".to_string(),
                    SymbolRef::new(Symbol::global(
                        AtomicType::Type,
                        "void".to_string(),
                        0,
                        Span::ZERO,
                        Vis::Public,
                    )),
                ),
                (
                    "_".to_string(),
                    SymbolRef::new(Symbol::global(
                        AtomicType::Unknown,
                        "_".to_string(),
                        0,
                        Span::ZERO,
                        Vis::Public,
                    )),
                ),
            ]),
            function_count: 0,
            global_count: 0,
            var_count: 0,
            arg_count: 0,
        }
    }
}

impl Default for SymbolMap {
    fn default() -> Self {
        SymbolMap::new()
    }
}

/// Symbol table.
///
/// The symbol table is a stack of hash maps. Each hashmap maps a name to a
/// symbol, the global scope is at level 0 and each scope we go deeper the
/// level increases by one.
#[derive(Clone)]
pub struct SymbolTable {
    /// all the tables, the first table is the always the global scope and as
    /// we go deeper in scopes we push new tables
    tabs: Vec<SymbolMap>,
}

impl SymbolTable {
    /// Create a new Symbol Table, with the global scope.
    pub fn new() -> SymbolTable {
        // TODO: load with atomic types like int, float etc etc
        SymbolTable {
            tabs: vec![SymbolMap::first_scope()],
        }
    }

    fn last_map(&self) -> &SymbolMap {
        // we can unwrap because we know there is at least the global scope.
        self.tabs.last().unwrap()
    }

    fn last_map_mut(&mut self) -> &mut SymbolMap {
        // we can unwrap because we know there is at least the global scope.
        self.tabs.last_mut().unwrap()
    }

    /// Enter a new scope
    pub fn scope_enter(&mut self) {
        self.tabs.push(SymbolMap::new())
    }

    /// Enter a new scope
    pub fn scope_exit(&mut self, sink: &mut DiagnosticSink) {
        assert_ne!(self.tabs.len(), 1, "can't exit out of the global scope");

        for symref in self.last_map().map.values() {
            let sym = symref.read().unwrap();

            // type annotation needed the type is unknown
            if sym.atomtyp == AtomicType::Unknown {
                sink.push(TypeAnnotationsNeeded {
                    loc: sym.loc.clone(),
                })
            }

            // unused symbol check
            if sym.vis != Vis::Public && sym.uses == 0 {
                // the symbol isn't global and isn't used so we push a warning
                sink.push(NeverUsedSymbol {
                    kind: sym.kind.clone(),
                    name: sym.name.clone(),
                    loc: sym.loc.clone(),
                })
            }
        }

        self.tabs.pop();
    }

    /// Bind a name to a symbol in the current scope, will panick if name == `_`
    pub fn bind(&mut self, name: String, symref: SymbolRef) -> Result<(), Diagnostic> {
        assert_ne!(name.as_str(), "_", "`_` is a reserved identifier");

        {
            // we create a new scope because we want sym to be dropped before we insert it
            let sym = symref.read().unwrap();

            match sym.kind {
                SymKind::Var { .. } => {
                    self.last_map_mut().var_count += 1;
                }
                SymKind::Arg => {
                    self.last_map_mut().arg_count += 1;
                }
                SymKind::Global => {
                    self.last_map_mut().global_count += 1;
                }
                SymKind::Function => {
                    if let Some(previous_symref) = self.lookup(&name, false) {
                        let previous_sym = previous_symref.read().unwrap();

                        if let SymKind::Function = previous_sym.kind {
                            return Err(NameDefinedMultipleTimes {
                                name: &name,
                                loc_previous: previous_sym.loc.clone(),
                                loc: sym.loc.clone(),
                            }
                            .into_diag());
                        }
                    }

                    self.last_map_mut().function_count += 1;
                }
            }
        }

        self.last_map_mut().map.insert(name, symref);

        Ok(())
    }

    /// Return the current scope level
    pub fn level(&self) -> usize {
        self.tabs.len() - 1
    }

    /// Lookup for the symbol in the current scope, returns None if there is no
    /// symbol with this name in the current scope
    pub fn lookup_current(&self, name: impl AsRef<str>) -> Option<SymbolRef> {
        self.last_map().map.get(name.as_ref()).cloned()
    }

    /// Lookup for a symbol with the given name, starting at the current scope
    /// ending at the global scope, returns None if there is no symbol in any
    /// scopes
    pub fn lookup(&mut self, name: impl AsRef<str>, used: bool) -> Option<SymbolRef> {
        let name = name.as_ref();
        for i in (0..=self.level()).rev() {
            if let Some(symref) = self.tabs[i].map.get(name) {
                let symref = symref.clone();
                if used {
                    symref.write().unwrap().uses += 1;
                }
                return Some(symref);
            }
        }
        None
    }

    /// Edit a symbol in the scope `which` with the name `name`, will panick if
    /// the scope or the symbol doesn't exist
    pub fn edit(&mut self, which: usize, name: impl AsRef<str>, new_symbol: Symbol) {
        let symref = self.tabs[which].map.get_mut(name.as_ref()).unwrap().clone();
        let mut lock = symref.write().unwrap();

        *lock = new_symbol;
    }

    /// Returns the Var count of the last symbol map
    pub fn var_count(&self) -> usize {
        self.last_map().var_count
    }

    /// Returns the Arg count of the last symbol map
    pub fn arg_count(&self) -> usize {
        self.last_map().arg_count
    }

    /// Returns the Global count of the last symbol map
    pub fn global_count(&self) -> usize {
        self.last_map().global_count
    }
}

impl Debug for SymbolTable {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_map().entries(self.tabs.iter().enumerate()).finish()
    }
}

impl Default for SymbolTable {
    fn default() -> Self {
        SymbolTable::new()
    }
}

#[derive(Debug, Clone)]
pub struct Loop {
    /// index of the loop
    index: usize,
    /// type of the loop
    atomtyp: AtomicType,
}

#[derive(Debug, Clone)]
pub struct LoopStack {
    loops: Vec<Loop>,
    index: usize,
}

impl LoopStack {
    pub fn new() -> LoopStack {
        LoopStack {
            loops: Vec::new(),
            index: 0,
        }
    }

    pub fn alloc_loop(&mut self) -> usize {
        let index = self.index;
        self.index += 1;

        self.loops.push(Loop {
            index,
            atomtyp: AtomicType::Unknown,
        });

        index
    }

    pub fn last(&self) -> Option<&Loop> {
        self.loops.last()
    }

    pub fn reset(&mut self) {
        self.index = 0;
        self.loops.clear();
    }

    pub fn get(&self, index: usize) -> Option<&Loop> {
        self.loops.iter().find(|r#loop| r#loop.index == index)
    }

    fn get_mut(&mut self, index: usize) -> Option<&mut Loop> {
        self.loops.iter_mut().find(|r#loop| r#loop.index == index)
    }

    pub fn set_atomtyp(&mut self, index: usize, atomtyp: AtomicType) {
        let Some(lop) = self.get_mut(index) else {
            panic!("loop at index {index} not found")
        };
        assert_ne!(
            atomtyp,
            AtomicType::Unknown,
            "can't set type of loop to Unknown"
        );
        assert_eq!(
            lop.atomtyp,
            AtomicType::Unknown,
            "can't set twice the atomic type of a loop"
        );

        lop.atomtyp = atomtyp;
    }
}

impl Default for LoopStack {
    fn default() -> Self {
        LoopStack::new()
    }
}
