// TODO: rename this pass to `post_checking`
use lunc_diag::ToDiagnostic;

use crate::diags::{Idk128, OverflowingLiteral};

use super::*;

/// Safety checks for the SCIR, checks for literals overflow and more
impl SemaChecker {
    pub fn safety_ck_mod(&mut self, module: &mut ScModule) {
        self.safety_ck_items(&mut module.items);
    }

    pub fn realpath(&self, item: &mut ScItem) {
        if let Some(sym) = item.symbol()
            && sym.inspect(|s| matches!(s.path.first().map(|s| s.as_str()), Some("orb")))
        {
            sym.inspect_mut(|sym| {
                *sym.path.first_mut().unwrap() = String::from(self.opts.orb_name());
            });
        }
    }

    pub fn safety_ck_items(&mut self, items: &mut [ScItem]) {
        for item in items {
            match self.safety_ck_item(item) {
                Ok(()) => {}
                Err(d) => {
                    self.sink.emit(d);
                }
            };
        }
    }

    pub fn safety_ck_item(&mut self, item: &mut ScItem) -> Result<(), Diagnostic> {
        self.realpath(item);

        match item {
            ScItem::GlobalDef {
                name: _,
                name_loc: _,
                mutability: _,
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
            ScItem::GlobalUninit {
                name: _,
                name_loc: _,
                typexpr,
                loc: _,
                sym: _,
            } => {
                self.safety_ck_expr(typexpr)?;

                Ok(())
            }
            ScItem::FunDefinition {
                name: _,
                name_loc: _,
                typexpr,
                args,
                rettypexpr,
                body,
                info: FunDefInfo { defined_mut: _ },
                loc: _,
                sym: _,
            } => {
                if let Some(typexpr) = &**typexpr {
                    self.safety_ck_expr(typexpr)?;
                }

                for arg in args {
                    match self.safety_ck_arg(arg) {
                        Ok(()) => {}
                        Err(d) => {
                            self.sink.emit(d);
                        }
                    }
                }

                if let Some(rettyexpr) = rettypexpr {
                    self.safety_ck_expr(rettyexpr)?;
                }

                self.safety_ck_block(body);

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
                    self.safety_ck_expr(typexpr)?;
                }

                for arg in args {
                    match self.safety_ck_expr(arg) {
                        Ok(()) => {}
                        Err(d) => {
                            self.sink.emit(d);
                        }
                    }
                }

                if let Some(retty) = rettypexpr {
                    self.safety_ck_expr(retty)?;
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

    pub fn safety_ck_expr(&mut self, expr: &ScExpression) -> Result<(), Diagnostic> {
        match &expr.expr {
            ScExprKind::Lit(Lit {
                kind,
                value,
                tag: _,
            }) => match (kind, value) {
                (LitKind::Integer, LitVal::Int(int)) => {
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
                (LitKind::Float, LitVal::Float(float)) => {
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
                _ => Ok(()),
            },
            ScExprKind::BoolLit(_) | ScExprKind::Ident(_) => Ok(()),
            ScExprKind::Binary { lhs, op: _, rhs } => {
                self.safety_ck_expr(lhs)?;

                self.safety_ck_expr(rhs)?;

                Ok(())
            }
            ScExprKind::Unary { op: _, expr } | ScExprKind::Borrow(_, expr) => {
                self.safety_ck_expr(expr)?;

                Ok(())
            }
            ScExprKind::Call { callee, args } => {
                self.safety_ck_expr(callee)?;

                for arg in args {
                    self.safety_ck_expr(arg)?;
                }

                Ok(())
            }
            ScExprKind::If {
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
            ScExprKind::Block {
                label: _,
                block,
                index: _,
            }
            | ScExprKind::Loop {
                label: _,
                body: block,
                index: _,
            } => {
                self.safety_ck_block(block);

                Ok(())
            }
            ScExprKind::Return { expr }
            | ScExprKind::Break {
                label: _,
                expr,
                index: _,
            } => {
                if let Some(expr) = expr {
                    self.safety_ck_expr(expr)?;
                }

                Ok(())
            }
            ScExprKind::Continue { label: _, index: _ } | ScExprKind::Null => Ok(()),
            ScExprKind::Field { expr, member: _ } => {
                self.safety_ck_expr(expr)?;

                Ok(())
            }
            ScExprKind::QualifiedPath { path: _, sym: _ } | ScExprKind::Underscore => Ok(()),
            ScExprKind::PointerType(_, typexpr) => {
                self.safety_ck_expr(typexpr)?;

                Ok(())
            }
            ScExprKind::FunPtrType { args, ret } => {
                for arg in args {
                    match self.safety_ck_expr(arg) {
                        Ok(()) => {}
                        Err(d) => {
                            self.sink.emit(d);
                        }
                    }
                }

                if let Some(ret) = ret {
                    self.safety_ck_expr(ret)?;
                }

                Ok(())
            }
            ScExprKind::Poisoned { diag: _ } => Ok(()),
        }
    }

    pub fn safety_ck_block(&mut self, block: &ScBlock) {
        for stmt in &block.stmts {
            match self.safety_ck_stmt(stmt) {
                Ok(()) => {}
                Err(d) => {
                    self.sink.emit(d);
                }
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
            ScStmtKind::VariableDef {
                name: _,
                mutability: _,
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
            ScStmtKind::Defer { expr } | ScStmtKind::Expression(expr) => {
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
