use std::cell::RefCell;

use lunc_diag::ToDiagnostic;

use crate::diags::{Idk128, OverflowingLiteral};

use super::*;

/// Safety checks for the SCIR, checks for literals overflow and more
///
/// *It also populate the variables info of function definitions, see
/// [`FunDefInfo::variables`].*
impl SemaChecker {
    pub fn safety_ck_mod(&mut self, module: &mut ScModule) {
        self.safety_ck_items(&mut module.items);
    }

    pub fn safety_ck_items(&mut self, items: &mut [ScItem]) {
        for item in items {
            match self.safety_ck_item(item) {
                Ok(()) => {}
                Err(d) => self.sink.emit(d),
            };
        }
    }

    pub fn safety_ck_item(&mut self, item: &mut ScItem) -> Result<(), Diagnostic> {
        match item {
            ScItem::GlobalDef {
                name: _,
                name_loc: _,
                mutable: _,
                typexpr,
                value,
                loc: _,
                sym: _,
            } => {
                if let Some(typexpr) = &**typexpr {
                    self.safety_ck_expr(typexpr, None)?;
                }

                self.safety_ck_expr(value, None)?;

                Ok(())
            }
            ScItem::GlobalUninit {
                name: _,
                name_loc: _,
                typexpr,
                loc: _,
                sym: _,
            } => {
                self.safety_ck_expr(typexpr, None)?;

                Ok(())
            }
            ScItem::FunDefinition {
                name: _,
                name_loc: _,
                typexpr,
                args,
                rettypexpr,
                body,
                info:
                    FunDefInfo {
                        defined_mut: _,
                        variables,
                    },
                loc: _,
                sym: _,
            } => {
                if let Some(typexpr) = &**typexpr {
                    self.safety_ck_expr(typexpr, None)?;
                }

                for arg in args {
                    match self.safety_ck_arg(arg) {
                        Ok(()) => {}
                        Err(d) => self.sink.emit(d),
                    }
                }

                if let Some(rettyexpr) = rettypexpr {
                    self.safety_ck_expr(rettyexpr, None)?;
                }

                let vars = RefCell::new(Vec::new());
                self.safety_ck_block(body, Some(&vars));
                *variables = vars.into_inner();

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
                sym: _,
            } => {
                if let Some(typexpr) = &**typexpr {
                    self.safety_ck_expr(typexpr, None)?;
                }

                for arg in args {
                    match self.safety_ck_expr(arg, None) {
                        Ok(()) => {}
                        Err(d) => self.sink.emit(d),
                    }
                }

                if let Some(retty) = rettypexpr {
                    self.safety_ck_expr(retty, None)?;
                }

                Ok(())
            }
            ScItem::Module {
                name: _,
                module,
                loc: _,
                sym: _,
            } => {
                self.safety_ck_mod(module);

                Ok(())
            }
            ScItem::ExternBlock {
                abi: _,
                items,
                loc: _,
            } => {
                self.safety_ck_items(items);

                Ok(())
            }
        }
    }

    pub fn safety_ck_expr(
        &mut self,
        expr: &ScExpression,
        variables: Option<&RefCell<Vec<Symbol>>>,
    ) -> Result<(), Diagnostic> {
        match &expr.expr {
            ScExpr::IntLit(int) => {
                if expr.typ == Type::U128 {
                    return Ok(());
                }

                let range = expr.typ.integer_range(self.opts.target()).unwrap();

                let int: i128 = match (*int).try_into() {
                    Ok(i) => i,
                    Err(_) => {
                        let range = Idk128::I128(*range.start())..=Idk128::I128(*range.end());

                        return Err(OverflowingLiteral {
                            integer: Idk128::U128(*int),
                            typ: expr.typ.clone(),
                            range,
                            loc: expr.loc.clone().unwrap(),
                        }
                        .into_diag());
                    }
                };

                if !range.contains(&int) {
                    let range = Idk128::I128(*range.start())..=Idk128::I128(*range.end());

                    self.sink.emit(OverflowingLiteral {
                        integer: Idk128::I128(int),
                        typ: expr.typ.clone(),
                        range: range.clone(),
                        loc: expr.loc.clone().unwrap(),
                    });
                }

                Ok(())
            }
            ScExpr::FloatLit(float) => {
                let range = expr.typ.float_range().unwrap();

                if expr.typ == Type::F16 || expr.typ == Type::F128 {
                    self.sink.emit(feature_todo! {
                        feature: "f16 and f128 types",
                        label: "f16 and f128 types",
                        loc: expr.loc.clone().unwrap(),
                    });
                }

                if !range.contains(float) {
                    let range = Idk128::F64(*range.start())..=Idk128::F64(*range.end());

                    self.sink.emit(OverflowingLiteral {
                        integer: Idk128::F64(*float),
                        typ: expr.typ.clone(),
                        range,
                        loc: expr.loc.clone().unwrap(),
                    });
                }

                Ok(())
            }
            ScExpr::BoolLit(_) | ScExpr::StringLit(_) | ScExpr::CharLit(_) | ScExpr::Ident(_) => {
                Ok(())
            }
            ScExpr::Binary { lhs, op: _, rhs } => {
                self.safety_ck_expr(lhs, variables)?;

                self.safety_ck_expr(rhs, variables)?;

                Ok(())
            }
            ScExpr::Unary { op: _, expr } | ScExpr::Borrow { mutable: _, expr } => {
                self.safety_ck_expr(expr, variables)?;

                Ok(())
            }
            ScExpr::FunCall { callee, args } => {
                self.safety_ck_expr(callee, variables)?;

                for arg in args {
                    self.safety_ck_expr(arg, variables)?;
                }

                Ok(())
            }
            ScExpr::If {
                cond,
                then_br,
                else_br,
            } => {
                self.safety_ck_expr(cond, variables)?;

                self.safety_ck_expr(then_br, variables)?;
                if let Some(else_br) = else_br {
                    self.safety_ck_expr(else_br, variables)?;
                }

                Ok(())
            }
            ScExpr::Block {
                label: _,
                block,
                index: _,
            }
            | ScExpr::Loop {
                label: _,
                body: block,
                index: _,
            } => {
                self.safety_ck_block(block, variables);

                Ok(())
            }
            ScExpr::Return { expr }
            | ScExpr::Break {
                label: _,
                expr,
                index: _,
            } => {
                if let Some(expr) = expr {
                    self.safety_ck_expr(expr, variables)?;
                }

                Ok(())
            }
            ScExpr::Continue { label: _, index: _ } | ScExpr::Null => Ok(()),
            ScExpr::MemberAccess { expr, member: _ } => {
                self.safety_ck_expr(expr, variables)?;

                Ok(())
            }
            ScExpr::QualifiedPath { path: _, sym: _ } | ScExpr::Underscore => Ok(()),
            ScExpr::PointerType {
                mutable: _,
                typexpr,
            } => {
                self.safety_ck_expr(typexpr, variables)?;

                Ok(())
            }
            ScExpr::FunPtrType { args, ret } => {
                for arg in args {
                    match self.safety_ck_expr(arg, variables) {
                        Ok(()) => {}
                        Err(d) => self.sink.emit(d),
                    }
                }

                if let Some(ret) = ret {
                    self.safety_ck_expr(ret, variables)?;
                }

                Ok(())
            }
            ScExpr::Poisoned { diag: _ } => Ok(()),
        }
    }

    pub fn safety_ck_block(&mut self, block: &ScBlock, variables: Option<&RefCell<Vec<Symbol>>>) {
        for stmt in &block.stmts {
            match self.safety_ck_stmt(stmt, variables) {
                Ok(()) => {}
                Err(d) => self.sink.emit(d),
            }
        }

        if let Some(last) = &block.last_expr
            && let Err(d) = self.safety_ck_expr(last, variables)
        {
            self.sink.emit(d);
        }
    }

    pub fn safety_ck_stmt(
        &mut self,
        stmt: &ScStatement,
        variables: Option<&RefCell<Vec<Symbol>>>,
    ) -> Result<(), Diagnostic> {
        match &stmt.stmt {
            ScStmt::VariableDef {
                name: _,
                name_loc: _,
                mutable: _,
                typexpr,
                value,
                sym,
            } => {
                if let Some(typexpr) = typexpr {
                    self.safety_ck_expr(typexpr, variables)?;
                }

                self.safety_ck_expr(value, variables)?;

                if let Some(variables) = variables {
                    let mut variables = variables.borrow_mut();
                    variables.push(sym.clone());
                }

                Ok(())
            }
            ScStmt::Defer { expr } | ScStmt::Expression(expr) => {
                self.safety_ck_expr(expr, variables)?;

                Ok(())
            }
        }
    }

    pub fn safety_ck_arg(&mut self, arg: &ScArg) -> Result<(), Diagnostic> {
        let ScArg {
            name: _,
            name_loc: _,
            typexpr,
            loc: _,
            sym: _,
        } = arg;

        self.safety_ck_expr(typexpr, None)?;

        Ok(())
    }
}
