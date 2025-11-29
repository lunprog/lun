//! Type variable unifier -- Hindley–Milner type system

use crate::{diags::MismatchedTypes, eval::CtemBuilder};

use super::*;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TyVarProp {
    Integer,
    Float,
}

/// Type unifier of UTIR.
#[derive(Debug, Clone)]
pub struct Unifier {
    orb: Orb,
    substitutions: SparseMap<TyVar, Uty>,
    properties: SparseMap<TyVar, TyVarProp>,
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
            properties: SparseMap::new(),
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

    pub fn unify_con(&mut self, con: Con) {
        match con {
            Con::Uty(Uty::Expr(expr_l), Uty::Expr(expr_r), pre) => {
                let ctem_builder = self.take_ctem();

                let mut ctem = ctem_builder.build(&self.orb);

                let Some(typ_l) = ctem.evaluate_type(self.item.unwrap(), expr_l) else {
                    todo!("DIAGNOSTIC: EXPECTED TYPE GOT EXPRESSION")
                    // return;
                };

                let Some(typ_r) = ctem.evaluate_type(self.item.unwrap(), expr_r) else {
                    todo!("DIAGNOSTIC: EXPECTED TYPE GOT EXPRESSION")
                    // return;
                };

                self.ctem_builder = ctem.builder();

                if typ_l != typ_r {
                    self.sink()
                        .emit(MismatchedTypes::new(pre, Vec::new(), String::new()));
                    todo!(
                        "IMPLEMENT EXPRESSION PRETTY PRINT IN LUN SYNTAX FOR THE MISMATCHED TYPES ERROR"
                    )
                }
            }
            Con::Uty(Uty::TyVar(tyv_l), Uty::TyVar(tyv_r), _)
                if tyv_l == tyv_r && self.properties.get(tyv_l) == self.properties.get(tyv_r) => {}
            Con::Uty(ty, Uty::TyVar(tyvar), loc) => {
                if let Some(substitution) = self.substitutions.get(tyvar) {
                    self.unify_con(Con::Uty(ty, *substitution, loc));
                    return;
                }

                assert!(!self.occurs_in(tyvar, ty));
                self.substitutions.insert(tyvar, ty);
            }
            Con::Uty(Uty::TyVar(tyvar), ty, loc) => {
                if let Some(substitution) = self.substitutions.get(tyvar) {
                    self.unify_con(Con::Uty(ty, *substitution, loc));
                    return;
                }

                assert!(!self.occurs_in(tyvar, ty));
                self.substitutions.insert(tyvar, ty);
            }
            Con::Integer(uty, pre) => {
                if let Uty::TyVar(tyvar) = uty {
                    self.properties.insert(tyvar, TyVarProp::Integer);
                } else {
                    _ = pre;
                    todo!("CHECK TYPE IS ABLE TO BE AN INTEGER {uty:?}")
                }
            }
            Con::Float(uty, pre) => {
                if let Uty::TyVar(tyvar) = uty {
                    self.properties.insert(tyvar, TyVarProp::Float);
                } else {
                    _ = pre;
                    todo!("CHECK TYPE IS ABLE TO BE AN INTEGER {uty:?}")
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
            Uty::Expr(_) => false,
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
