//! Type variable unifier -- Hindley–Milner type system

use crate::{
    diags::{ExpectedTypeFoundExpr, MismatchedTypes},
    eval::CtemBuilder,
    pretty::lun,
};

use super::*;

/// Type unifier of UTIR.
#[derive(Debug, Clone)]
pub struct Unifier {
    orb: Orb,
    substitutions: SparseMap<TyVar, Uty>,
    ctem_builder: CtemBuilder,
    /// current item that we unify, used for evaluation of types.
    item: Opt<ItemId>,
}

impl Unifier {
    /// Create a new unifier.
    pub fn new(orb: Orb, sink: DiagnosticSink) -> Unifier {
        Unifier {
            orb,
            substitutions: SparseMap::new(),
            ctem_builder: CtemBuilder::new(sink),
            item: Opt::None,
        }
    }

    /// Unifies everything and substitute the types
    pub fn unify(&mut self) {
        for item in self.orb.items.entity_iter() {
            self.item = Opt::Some(item);
            self.unify_body(item);
        }
    }

    pub fn unify_body(&mut self, item: ItemId) {
        let body = self.orb.items.get(item).body();
        let constraints = body.constraints.clone();

        for con in constraints.0.iter() {
            self.unify_con(con.clone());
        }
    }

    fn expr_to_string(&self, expr: ExprId) -> String {
        lun::expr_to_string(expr, self.item.unwrap(), &self.orb)
    }

    fn expr_loc(&self, expr: ExprId) -> Span {
        self.orb
            .items
            .get(self.item.unwrap())
            .body()
            .expr_locs
            .get(expr)
            .cloned()
            .unwrap_or_default()
    }

    pub fn unify_con(&mut self, con: Con) {
        match con {
            Con {
                lhs: Uty::Expr(expr_l),
                rhs: Uty::Expr(expr_r),
                pre,
            } => {
                let ctem_builder = self.take_ctem();

                let mut ctem = ctem_builder.build(&self.orb);

                let Some(typ_l) = ctem.evaluate_type(self.item.unwrap(), expr_l) else {
                    let loc = self.expr_loc(expr_l);
                    self.sink().emit(ExpectedTypeFoundExpr { loc });

                    return;
                };

                let Some(typ_r) = ctem.evaluate_type(self.item.unwrap(), expr_r) else {
                    let loc = self.expr_loc(expr_r);
                    self.sink().emit(ExpectedTypeFoundExpr { loc });

                    return;
                };

                self.ctem_builder = ctem.builder();

                if typ_l != typ_r {
                    let expected_str = self.expr_to_string(expr_r);
                    let found_str = self.expr_to_string(expr_l);

                    self.sink()
                        .emit(MismatchedTypes::new(pre, vec![expected_str], found_str));
                }
            }
            Con {
                lhs: Uty::Expr(expr),
                rhs: ability_uty @ (Uty::Integer | Uty::Float),
                pre,
            }
            | Con {
                lhs: ability_uty @ (Uty::Integer | Uty::Float),
                rhs: Uty::Expr(expr),
                pre,
            } => {
                let ctem_builder = self.take_ctem();

                let mut ctem = ctem_builder.build(&self.orb);

                let Some(type_expr) = ctem.evaluate_type(self.item.unwrap(), expr) else {
                    let loc = self.expr_loc(expr);
                    self.sink().emit(ExpectedTypeFoundExpr { loc });

                    return;
                };

                self.ctem_builder = ctem.builder();

                let ability = TypeAbility::from_uty(ability_uty);

                if !type_expr.has_ability(ability) {
                    let expr_str = self.expr_to_string(expr);
                    let ability_str = ability.to_string();

                    self.sink()
                        .emit(MismatchedTypes::new(pre, vec![ability_str], expr_str));
                }
            }
            Con {
                lhs: Uty::TyVar(tyv_l),
                rhs: Uty::TyVar(tyv_r),
                pre: _,
            } if tyv_l == tyv_r => {}
            Con {
                lhs: Uty::TyVar(tyvar),
                rhs: ty,
                pre,
            } => {
                if let Some(substitution) = self.substitutions.get(tyvar) {
                    self.unify_con(Con {
                        lhs: *substitution,
                        rhs: ty,
                        pre,
                    });
                    return;
                }

                assert!(!self.occurs_in(tyvar, ty));
                self.substitutions.insert(tyvar, ty);
            }
            Con {
                lhs: ty,
                rhs: Uty::TyVar(tyvar),
                pre,
            } => {
                if let Some(substitution) = self.substitutions.get(tyvar) {
                    self.unify_con(Con {
                        lhs: ty,
                        rhs: *substitution,
                        pre,
                    });
                    return;
                }

                assert!(!self.occurs_in(tyvar, ty));
                self.substitutions.insert(tyvar, ty);
            }
            Con {
                lhs: lhs_uty @ (Uty::Integer | Uty::Float),
                rhs: rhs_uty @ (Uty::Integer | Uty::Float),
                pre,
            } => {
                if lhs_uty != rhs_uty {
                    let lhs = lhs_uty.to_string();
                    let rhs = rhs_uty.to_string();

                    self.sink().emit(MismatchedTypes::new(pre, vec![rhs], lhs));
                }
            }
        }
    }

    pub fn occurs_in(&self, tyvar: TyVar, ty: Uty) -> bool {
        match ty {
            Uty::TyVar(v) => {
                if let Some(substitution) = self.substitutions.get(v)
                    && *substitution != Uty::TyVar(v)
                {
                    return self.occurs_in(tyvar, *substitution);
                }

                tyvar == v
            }
            Uty::Integer | Uty::Float | Uty::Expr(_) => false,
        }
    }

    pub fn substitutions(&self) -> &SparseMap<TyVar, Uty> {
        &self.substitutions
    }

    fn sink(&mut self) -> &mut DiagnosticSink {
        &mut self.ctem_builder.sink
    }

    pub fn take_orb(&mut self) -> Orb {
        mem::take(&mut self.orb)
    }

    pub fn take_ctem(&mut self) -> CtemBuilder {
        let sink = self.ctem_builder.sink.clone();

        mem::replace(&mut self.ctem_builder, CtemBuilder::new(sink))
    }
}
