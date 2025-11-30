//! Compile-time evaluation machinery of UTIR.

use std::{
    collections::HashMap,
    hash::{BuildHasher, RandomState},
    mem,
};

use lunc_diag::DiagnosticSink;
use lunc_entity::Opt;
use lunc_seq::sir::{self, PrimType};
use lunc_utils::Span;

use crate::diags::CantEvaluateAtComptime;

use super::utir;

/// Builder of [`UtirCtem`] keeps track of the modifications of the Orb, it will
/// clear the memoized evaluation if the new Orb is different from the old one.
#[derive(Debug, Clone)]
pub struct CtemBuilder {
    memo: HashMap<(utir::ItemId, utir::ExprId), UtirValue>,
    pub(crate) sink: DiagnosticSink,
    old_hash: Option<u64>,
    hash_builder: RandomState,
}

impl CtemBuilder {
    /// Create a new empty builder.
    pub fn new(sink: DiagnosticSink) -> CtemBuilder {
        CtemBuilder {
            memo: HashMap::new(),
            sink,
            old_hash: None,
            hash_builder: RandomState::new(),
        }
    }

    /// Build a [UtirCtem].
    pub fn build<'utir>(self, orb: &'utir utir::Orb) -> UtirCtem<'utir> {
        // hash of the provided orb.
        let this_hash = self.hash_builder.hash_one(orb);

        let memo = if let Some(old_hash) = self.old_hash
            && old_hash == this_hash
        {
            // the old orb and the provided one are the same, we re-use the old memo
            self.memo
        } else {
            HashMap::new()
        };

        UtirCtem {
            orb,
            sink: self.sink,
            item: Opt::None,
            emit_diag: true,
            loc: Span::ZERO,
            memo,
        }
    }
}

/// Maybe untyped value, used to represent untyped integer and float literals.
///
/// # Types
///
/// Because UtirValue is working with UTIR, we cannot use the
/// `CValue::Type(Type)` yet because we don't know the id's of the SIR items, so
/// an UtirValue can never have `UtirValue::CVal(CValue::Type(...))` value.
///
/// Instead at this stage we used `UtirValue::Type(utir::Type...)`.
#[derive(Debug, Clone, PartialEq)]
pub enum UtirValue {
    CVal(sir::CValue),
    Type(utir::Type),
    Int(u128),
    Float(f64),
}

impl From<sir::CValue> for UtirValue {
    fn from(value: sir::CValue) -> Self {
        UtirValue::CVal(value)
    }
}

/// UTIR **c**ompile-**t**ime **e**valuation **m**achinery.
///
/// # Note
///
/// This evaluator performs untyped evaluation: it will try to do its best even
/// when the type normally don't match, because the orb will be type checked
/// later and the errors will be emitted later.
#[derive(Debug, Clone)]
pub struct UtirCtem<'utir> {
    orb: &'utir utir::Orb,
    sink: DiagnosticSink,
    /// current item that we evaluate in.
    item: Opt<utir::ItemId>,
    emit_diag: bool,
    /// location of the top most thing we try to evaluate
    loc: Span,
    /// Memoized results
    memo: HashMap<(utir::ItemId, utir::ExprId), UtirValue>,
}

impl<'utir> UtirCtem<'utir> {
    /// Create a new UtirCtem with the orb and the sink.
    pub fn new(orb: &'utir utir::Orb, sink: DiagnosticSink) -> UtirCtem<'utir> {
        UtirCtem {
            orb,
            sink,
            item: Opt::None,
            emit_diag: true,
            loc: Span::ZERO,
            memo: HashMap::new(),
        }
    }

    fn current_item(&self) -> &utir::Item {
        self.orb.items.get(self.item.unwrap())
    }

    fn get_expr(&mut self, expr: utir::ExprId) -> utir::Expr {
        self.current_item().body().exprs.get(expr).clone()
    }

    fn get_expr_loc(&self, expr: utir::ExprId) -> Option<Span> {
        self.current_item().body().expr_locs.get(expr).cloned()
    }

    fn get_expr_type(&self, expr: utir::ExprId) -> Option<utir::Uty> {
        self.current_item().body().expr_t.get(expr).copied()
    }

    /// Tries to evaluate the expression `expr` in the item `item`.
    ///
    /// # Errors
    ///
    /// If this function in unable to evaluate the expression at compile-time it
    /// will return `None` and maybe emit a diagnostic.
    pub fn evaluate_expr(&mut self, item: utir::ItemId, expr: utir::ExprId) -> Option<UtirValue> {
        let old_item = self.item;
        let old_loc = mem::replace(&mut self.loc, Span::ZERO);

        self.item = Opt::Some(item);

        let expr_loc = self.get_expr_loc(expr).unwrap_or_default();

        let res = match self._eval_expr(expr) {
            Ok(v) => Some(v),

            Err((loc, note)) => {
                self.sink.emit(CantEvaluateAtComptime {
                    note,
                    loc_expr: expr_loc,
                    loc,
                });

                None
            }
        };

        self.item = old_item;
        self.loc = old_loc;

        res
    }

    /// Tries to evaluate an expression as a type.
    ///
    /// # On failure
    ///
    /// Note that on failutre it just returns `None`, it doesn't emit a
    /// diagnostic (unable to evaluate at compile-time) this is so that you
    /// can emit in type-checking the "expected type but got an expression"
    /// diagnostic.
    pub fn evaluate_type(&mut self, item: utir::ItemId, typ: utir::ExprId) -> Option<utir::Type> {
        let old_emit = self.emit_diag;
        self.emit_diag = false;

        let res = match self.evaluate_expr(item, typ) {
            Some(UtirValue::Type(t)) => Some(t),
            Some(_) | None => None,
        };

        self.emit_diag = old_emit;

        res
    }

    /// Tries to evaluate the expression, return `None` if it can't evaluate at
    /// compile-time and NEVER emits a diagnostic.
    fn try_eval_expr(&mut self, expr: utir::ExprId) -> Result<UtirValue, (Span, Option<String>)> {
        self._eval_expr(expr)
    }

    /// Tries to evaluate the expression as a type, it it fails it returns the
    /// `void` type.
    fn try_eval_type(&mut self, expr: utir::ExprId) -> utir::Type {
        match self.try_eval_expr(expr) {
            Ok(UtirValue::Type(typ)) => typ,
            Ok(_) => utir::Type::PrimType(PrimType::Void),
            // NOTE: we don't emit a diag here because we will emit one in the
            // type-checking
            Err((loc, note)) => {
                self.sink.emit(CantEvaluateAtComptime {
                    note,
                    loc_expr: self.get_expr_loc(expr).unwrap(),
                    loc,
                });

                utir::Type::PrimType(PrimType::Void)
            }
        }
    }

    fn _eval_expr(&mut self, id: utir::ExprId) -> Result<UtirValue, (Span, Option<String>)> {
        if let Some(res) = self.memo.get(&(self.item.unwrap(), id)) {
            return Ok(res.clone());
        }

        let expr_loc = self.get_expr_loc(id).unwrap_or_default();
        let expr_t = self.get_expr_type(id);

        let expr_t = if let Some(utir::Uty::Expr(expr)) = expr_t
            && id != expr
        // TODO: this prevents a stack overflow when we try to evaluate the type
        // of type, because it's self-referential (in expr_t, eN: eN),
        {
            // NOTE: this is used by the eval to use as less as possible of
            // UntypedValue other than UntypedValue::Typed.
            Some(self.try_eval_type(expr))
        } else {
            None
        };

        let expr = self.get_expr(id);

        let res = match expr {
            utir::Expr::Int(i) => match expr_t {
                Some(utir::Type::PrimType(ptype)) => match ptype {
                    PrimType::I8 => Ok(sir::CValue::I8(i as i8).into()),
                    PrimType::I16 => Ok(sir::CValue::I16(i as i16).into()),
                    PrimType::I32 => Ok(sir::CValue::I32(i as i32).into()),
                    PrimType::I64 => Ok(sir::CValue::I64(i as i64).into()),
                    PrimType::I128 => Ok(sir::CValue::I128(i as i128).into()),
                    PrimType::Isz => Ok(sir::CValue::isz64(i as i64).into()),
                    PrimType::U8 => Ok(sir::CValue::U8(i as u8).into()),
                    PrimType::U16 => Ok(sir::CValue::U16(i as u16).into()),
                    PrimType::U32 => Ok(sir::CValue::U32(i as u32).into()),
                    PrimType::U64 => Ok(sir::CValue::U64(i as u64).into()),
                    PrimType::U128 => Ok(sir::CValue::U128(i).into()),
                    PrimType::Usz => Ok(sir::CValue::usz64(i as u64).into()),
                    _ => Ok(UtirValue::Int(i)),
                },
                _ => Ok(UtirValue::Int(i)),
            },
            utir::Expr::Char(c) => Ok(sir::CValue::Char(c).into()),
            utir::Expr::Float(f) => match expr_t {
                Some(utir::Type::PrimType(ptype)) => match ptype {
                    PrimType::F32 => Ok(sir::CValue::F32(f.into_f64() as f32).into()),
                    PrimType::F64 => Ok(sir::CValue::F64(f.into_f64()).into()),
                    _ => Ok(UtirValue::Float(f.into_f64())),
                },
                _ => Ok(UtirValue::Float(f.into_f64())),
            },
            utir::Expr::Str(s) => Ok(sir::CValue::Str(s.clone()).into()),
            utir::Expr::CStr(s) => Ok(sir::CValue::CStr(s.clone()).into()),
            utir::Expr::Bool(b) => Ok(sir::CValue::Bool(b).into()),
            utir::Expr::PtrType(mutability, pointee) => {
                let pointee_t = self.try_eval_type(pointee);

                Ok(UtirValue::Type(utir::Type::Ptr(
                    mutability,
                    Box::new(pointee_t),
                )))
            }
            utir::Expr::FunptrType(params, ret) => {
                // NOTE: again no diag emitted, we will emit one in
                // type-checking.

                let (params_t, ret_t) = self.eval_funlike_type(params, ret);

                Ok(UtirValue::Type(utir::Type::FunPtr(
                    params_t,
                    Box::new(ret_t),
                )))
            }
            utir::Expr::PrimType(ptype) => Ok(UtirValue::Type(utir::Type::PrimType(ptype))),
            utir::Expr::FundefType {
                fundef,
                params,
                ret,
            } => {
                let (params, ret_t) = self.eval_funlike_type(params, Opt::Some(ret));

                Ok(UtirValue::Type(utir::Type::FunDef {
                    fundef,
                    params,
                    ret: Box::new(ret_t),
                }))
            }
            e => {
                if cfg!(debug_assertions) {
                    Err((expr_loc, Some(format!("DEBUG: {e:?} isn't able to eval."))))
                } else {
                    Err((expr_loc, None))
                }
            }
        }?;

        self.memo.insert((self.item.unwrap(), id), res.clone());

        Ok(res)
    }

    fn eval_funlike_type(
        &mut self,
        params: Vec<utir::ExprId>,
        ret: Opt<utir::ExprId>,
    ) -> (Vec<utir::Type>, utir::Type) {
        let mut args_t = Vec::with_capacity(params.len());

        for arg in params {
            args_t.push(self.try_eval_type(arg));
        }

        let ret_t = if let Some(ret) = ret.expand() {
            self.try_eval_type(ret)
        } else {
            utir::Type::PrimType(PrimType::Void)
        };

        (args_t, ret_t)
    }

    /// Convert this evaluation machine to a builder.
    pub fn builder(self) -> CtemBuilder {
        let hash_builder = RandomState::new();

        let old_hash = Some(hash_builder.hash_one(self.orb));

        CtemBuilder {
            memo: self.memo,
            sink: self.sink,
            old_hash,
            hash_builder,
        }
    }
}
