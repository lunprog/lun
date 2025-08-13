//! Safety checks for the SCIR, checks for literals overflow and more

use lunc_diag::ToDiagnostic;

use crate::diags::{Idk128, OverflowingLiteral};

use super::*;

impl SemaChecker {
    pub fn safety_ck_mod(&mut self, module: &ScModule) {
        self.safety_ck_items(&module.items);
    }

    pub fn safety_ck_items(&mut self, items: &[ScItem]) {
        for item in items {
            match self.safety_ck_item(item) {
                Ok(()) => {}
                Err(d) => self.sink.emit(d),
            };
        }
    }

    pub fn safety_ck_item(&mut self, item: &ScItem) -> Result<(), Diagnostic> {
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
                    self.safety_ck_expr(typexpr)?;
                }

                self.safety_ck_expr(value)?;

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

    pub fn safety_ck_expr(&mut self, expr: &ScExpression) -> Result<(), Diagnostic> {
        match &expr.expr {
            ScExpr::IntLit(int) => {
                if expr.typ == Type::U128 {
                    return Ok(());
                }

                let range = expr.typ.integer_range(&self.target).unwrap();

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
                self.safety_ck_expr(lhs)?;
                self.safety_ck_expr(rhs)?;

                Ok(())
            }
            ScExpr::Unary { op: _, expr } | ScExpr::Borrow { mutable: _, expr } => {
                self.safety_ck_expr(expr)?;

                Ok(())
            }
            ScExpr::FunCall { callee, args } => {
                self.safety_ck_expr(callee)?;

                for arg in args {
                    self.safety_ck_expr(arg)?;
                }

                Ok(())
            }
            ScExpr::If {
                cond,
                then_br,
                else_br,
            } => {
                self.safety_ck_expr(cond)?;

                self.safety_ck_expr(then_br)?;
                if let Some(else_br) = else_br {
                    self.safety_ck_expr(else_br)?;
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
                self.safety_ck_block(block);

                Ok(())
            }
            ScExpr::Return { expr }
            | ScExpr::Break {
                label: _,
                expr,
                index: _,
            } => {
                if let Some(expr) = expr {
                    self.safety_ck_expr(expr)?;
                }

                Ok(())
            }
            ScExpr::Continue { label: _, index: _ } | ScExpr::Null => Ok(()),
            ScExpr::MemberAccess { expr, member: _ } => {
                self.safety_ck_expr(expr)?;

                Ok(())
            }
            ScExpr::QualifiedPath { path: _, sym: _ } | ScExpr::Underscore => Ok(()),
            ScExpr::FunDefinition {
                args,
                rettypexpr,
                body,
            } => {
                for arg in args {
                    match self.safety_ck_arg(arg) {
                        Ok(()) => {}
                        Err(d) => self.sink.emit(d),
                    }
                }

                if let Some(rettyexpr) = rettypexpr {
                    self.safety_ck_expr(rettyexpr)?;
                }

                self.safety_ck_block(body);

                Ok(())
            }
            ScExpr::FunDeclaration { args, rettypexpr } => {
                for arg in args {
                    match self.safety_ck_expr(arg) {
                        Ok(()) => {}
                        Err(d) => self.sink.emit(d),
                    }
                }

                if let Some(retty) = rettypexpr {
                    self.safety_ck_expr(retty)?;
                }

                Ok(())
            }
            ScExpr::PointerType {
                mutable: _,
                typexpr,
            } => {
                self.safety_ck_expr(typexpr)?;

                Ok(())
            }
            ScExpr::FunPtrType { args, ret } => {
                for arg in args {
                    match self.safety_ck_expr(arg) {
                        Ok(()) => {}
                        Err(d) => self.sink.emit(d),
                    }
                }

                if let Some(ret) = ret {
                    self.safety_ck_expr(ret)?;
                }

                Ok(())
            }
        }
    }

    pub fn safety_ck_block(&mut self, block: &ScBlock) {
        for stmt in &block.stmts {
            match self.safety_ck_stmt(stmt) {
                Ok(()) => {}
                Err(d) => self.sink.emit(d),
            }
        }

        if let Some(last) = &block.last_expr
            && let Err(d) = self.safety_ck_expr(last)
        {
            self.sink.emit(d);
        }
    }

    pub fn safety_ck_stmt(&mut self, stmt: &ScStatement) -> Result<(), Diagnostic> {
        match &stmt.stmt {
            ScStmt::VariableDef {
                name: _,
                name_loc: _,
                mutable: _,
                typexpr,
                value,
                sym: _,
            } => {
                if let Some(typexpr) = typexpr {
                    self.safety_ck_expr(typexpr)?;
                }

                self.safety_ck_expr(value)?;

                Ok(())
            }
            ScStmt::Defer { expr } | ScStmt::Expression(expr) => {
                self.safety_ck_expr(expr)?;

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

        self.safety_ck_expr(typexpr)?;

        Ok(())
    }
}
