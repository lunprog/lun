//! Type variable unifier -- Hindley–Milner type system

use lunc_diag::DiagGuaranteed;
use lunc_entity::TightMap;

use crate::{diags::MismatchedTypes, eval::CtemBuilder, pretty::lun};

use super::*;

/// Type unifier of UTIR.
#[derive(Debug, Clone)]
pub struct Unifier {
    orb: Orb,
    /// current substitutions, **when unifying**
    substitutions: SparseMap<TyVar, Uty>,
    all_subs: TightMap<ItemId, SparseMap<TyVar, Uty>>,
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
            // NOTE: here we can use a tight-map because we go through the items
            // in order.
            all_subs: TightMap::new(),
            ctem_builder: CtemBuilder::new(sink),
            item: Opt::None,
        }
    }

    /// Unifies everything and substitute the types
    pub fn unify(&mut self) {
        self.orb.flavor.set_next();

        assert_eq!(self.orb.flavor, Flavor::Unified);

        for item in self.orb.items.entity_iter() {
            self.item = Opt::Some(item);
            self.unify_body(item);

            let substitutions = self.take_subs();
            self.all_subs.insert(item, substitutions);
        }
    }

    fn unify_body(&mut self, item: ItemId) {
        let body = self.orb.items.get(item).body();
        let constraints = body.constraints.clone();

        for con in constraints.0.iter() {
            _ = self.unify_con(con.clone());
        }
    }

    fn expr_to_string(&self, expr: ExprId) -> String {
        lun::expr_to_string(expr, self.item.unwrap(), &self.orb)
    }

    /// Returns `Some(DiagGuaranteed)` if it emitted a diagnostic, otherwise
    /// `None`.
    #[must_use]
    fn unify_con(&mut self, con: Con) -> Option<DiagGuaranteed> {
        match con {
            Con {
                lhs: Uty::Expr(expr_l),
                rhs: Uty::Expr(expr_r),
                pre,
            } => {
                let ctem_builder = self.take_ctem();

                let mut ctem = ctem_builder.build(&self.orb);

                let Some(typ_l) = ctem.evaluate_type(self.item.unwrap(), expr_l) else {
                    // NOTE: we don't throw an error because we will in the
                    // typeck stage, re typecheck everything and if it really
                    // can't work we throw the error.
                    return None;
                };

                let Some(typ_r) = ctem.evaluate_type(self.item.unwrap(), expr_r) else {
                    // NOTE: same as above.
                    return None;
                };

                self.ctem_builder = ctem.builder();

                if typ_l != typ_r
                    // TODO: this is kinda hackish maybe we should have a
                    // prettier way of handling `never` types.
                    && typ_l != Type::PrimType(PrimType::Never)
                    && typ_r != Type::PrimType(PrimType::Never)
                {
                    let expected_str = self.expr_to_string(expr_r);
                    let found_str = self.expr_to_string(expr_l);

                    Some(
                        self.sink()
                            .emit(MismatchedTypes::new(pre, vec![expected_str], found_str)),
                    )
                } else {
                    None
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
                    // NOTE: see the comments above.
                    return None;
                };

                self.ctem_builder = ctem.builder();

                let ability = TypeAbility::from_uty(ability_uty);

                if !type_expr.has_ability(ability) {
                    let expr_str = self.expr_to_string(expr);
                    let ability_str = ability.to_string();

                    Some(
                        self.sink()
                            .emit(MismatchedTypes::new(pre, vec![expr_str], ability_str)),
                    )
                } else {
                    None
                }
            }
            Con {
                lhs: Uty::TyVar(tyv_l),
                rhs: Uty::TyVar(tyv_r),
                pre: _,
            } if tyv_l == tyv_r => None,
            Con {
                lhs: Uty::TyVar(tyvar),
                rhs: ty,
                pre,
            } => {
                let errored = if let Some(substitution) = self.substitutions.get(tyvar).copied() {
                    let errored = self.unify_con(Con {
                        lhs: substitution,
                        rhs: ty,
                        pre,
                    });

                    if substitution.is_strong() {
                        return errored;
                    }

                    errored
                } else {
                    None
                };

                assert!(!self.occurs_in(tyvar, ty));
                if errored.is_none() {
                    self.substitutions.insert(tyvar, ty);
                }

                errored
            }
            Con {
                lhs: ty,
                rhs: Uty::TyVar(tyvar),
                pre,
            } => {
                let errored = if let Some(substitution) = self.substitutions.get(tyvar).copied() {
                    let errored = self.unify_con(Con {
                        lhs: ty,
                        rhs: substitution,
                        pre,
                    });

                    if substitution.is_strong() {
                        return errored;
                    }
                    errored
                } else {
                    None
                };

                assert!(!self.occurs_in(tyvar, ty));
                if errored.is_none() {
                    self.substitutions.insert(tyvar, ty);
                }

                errored
            }
            Con {
                lhs: lhs_uty @ (Uty::Integer | Uty::Float),
                rhs: rhs_uty @ (Uty::Integer | Uty::Float),
                pre,
            } => {
                if lhs_uty != rhs_uty {
                    let lhs = lhs_uty.to_string();
                    let rhs = rhs_uty.to_string();

                    Some(self.sink().emit(MismatchedTypes::new(pre, vec![rhs], lhs)))
                } else {
                    None
                }
            }
        }
    }

    fn occurs_in(&self, tyvar: TyVar, ty: Uty) -> bool {
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

    pub fn take_substitutions(&mut self) -> TightMap<ItemId, SparseMap<TyVar, Uty>> {
        mem::take(&mut self.all_subs)
    }

    fn sink(&mut self) -> &mut DiagnosticSink {
        &mut self.ctem_builder.sink
    }

    fn take_subs(&mut self) -> SparseMap<TyVar, Uty> {
        mem::take(&mut self.substitutions)
    }

    pub fn take_orb(&mut self) -> Orb {
        mem::take(&mut self.orb)
    }

    pub fn take_ctem(&mut self) -> CtemBuilder {
        let sink = self.ctem_builder.sink.clone();

        mem::replace(&mut self.ctem_builder, CtemBuilder::new(sink))
    }
}

/// Substituter -- takes the output of the [Unifier] and the [utir::Orb] and
/// substitute the type-variables.
#[derive(Debug, Clone)]
pub struct Substituter {
    subs: TightMap<ItemId, SparseMap<TyVar, Uty>>,
    /// current item we are substituting.
    item: Opt<ItemId>,

    // ITEM SPECIFIC
    i32_expr: Opt<ExprId>,
    f32_expr: Opt<ExprId>,
}

impl Substituter {
    pub fn new(subs: TightMap<ItemId, SparseMap<TyVar, Uty>>) -> Substituter {
        Substituter {
            subs,
            item: Opt::None,
            i32_expr: Opt::None,
            f32_expr: Opt::None,
        }
    }

    fn cur_subs(&self) -> &SparseMap<TyVar, Uty> {
        self.subs.get(self.item.unwrap()).unwrap()
    }

    pub fn substitute(&mut self, orb: &mut Orb) {
        for id in orb.items.entity_iter() {
            self.item = Opt::Some(id);

            let item = orb.items.get_mut(id);

            self.substitute_body(item.body_mut());

            match item {
                Item::Fundef(Fundef {
                    name: _,
                    path: _,
                    typ: _,
                    params,
                    ret_ty: _,
                    entry: _,
                    body: _,
                    loc: _,
                }) => {
                    for (_, param) in params.iter_mut() {
                        param.typ = Uty::Expr(self.sub(param.typ));
                    }
                }
                Item::Fundecl(_)
                | Item::GlobalUninit(_)
                | Item::Module(_)
                | Item::ExternBlock(_) => {}
                Item::GlobalDef(GlobalDef {
                    name: _,
                    path: _,
                    mutability: _,
                    typ,
                    value: _,
                    body: _,
                    loc: _,
                }) => {
                    *typ = Uty::Expr(self.sub(*typ));
                }
            }

            self.clear_item_specific();
        }
    }

    fn clear_item_specific(&mut self) {
        self.i32_expr = Opt::None;
        self.f32_expr = Opt::None;
    }

    fn substitute_body(&mut self, body: &mut Body) {
        let Body {
            labels: _,
            bindings,
            stmts: _,
            exprs,
            blocks: _,
            expr_t,
            type_vars,
            constraints,
            expr_locs: _,
            stmt_locs: _,
        } = body;

        for (_, binding) in bindings.iter_mut() {
            binding.typ = Uty::Expr(self.sub(binding.typ));
        }

        // it's super dump but we can't do differently without being dumber
        let i32_e = exprs.create(Expr::PrimType(PrimType::I32));
        self.i32_expr = Opt::Some(i32_e);
        let f32_e = exprs.create(Expr::PrimType(PrimType::F32));
        self.f32_expr = Opt::Some(f32_e);

        for (_, expr) in exprs.iter_mut() {
            if let Expr::ExtType(Ext { item, ent: typ }) = expr {
                let old = self.item;
                self.item = Opt::Some(*item);

                *expr = Expr::ExtExpr(Ext {
                    item: *item,
                    ent: self.sub(*typ),
                });

                self.item = old;
            }
        }

        for (_, typ) in expr_t.iter_mut() {
            *typ = Uty::Expr(self.sub(*typ));
        }

        constraints.0.clear();
        mem::take(type_vars);
    }

    /// Substitute the type-variables by something else than `Uty::TyVar(..)`.
    fn sub(&mut self, uty: Uty) -> ExprId {
        let typ = match uty {
            Uty::Expr(_) => uty,
            Uty::TyVar(tyvar) => {
                if let Some(typ) = self.cur_subs().get(tyvar) {
                    Uty::Expr(self.sub(*typ))
                } else {
                    uty
                }
            }
            Uty::Integer => {
                if let Some(i32) = self.i32_expr.expand() {
                    Uty::Expr(i32)
                } else {
                    // SAFETY: caller guarantees
                    opt_unreachable!()
                }
            }
            Uty::Float => {
                if let Some(f32) = self.f32_expr.expand() {
                    Uty::Expr(f32)
                } else {
                    // SAFETY: caller guarantees
                    opt_unreachable!()
                }
            }
        };

        match typ {
            Uty::Expr(e) => e,
            Uty::TyVar(tyvar) => {
                panic!(
                    "unable to substitute type-variable {tyvar} in {}",
                    self.item.unwrap()
                );
            }
            Uty::Float | Uty::Integer => {
                // if we had an integer/float we re-substitute, to have the
                // corresponding type-expression
                self.sub(typ)
            }
        }
    }
}
