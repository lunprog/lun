//! Compile-time evaluation machinery of UTIR.

use std::{
    collections::HashMap,
    hash::{BuildHasher, RandomState},
    mem,
};

use lunc_diag::DiagnosticSink;
use lunc_entity::Opt;
use lunc_seq::sir::{CValue, PrimType, Type};
use lunc_utils::Span;

use crate::diags::CantEvaluateAtComptime;

use super::utir::*;

/// Builder of [`UtirCtem`] keeps track of the modifications of the Orb, it will
/// clear the memoized evaluation if the new Orb is different from the old one.
#[derive(Debug, Clone)]
pub struct CtemBuilder {
    memo: HashMap<(ItemId, ExprId), UntypedValue>,
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
    pub fn build<'utir>(self, orb: &'utir Orb) -> UtirCtem<'utir> {
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
#[derive(Debug, Clone, PartialEq)]
pub enum UntypedValue {
    Typed(CValue),
    Int(u128),
    Float(f64),
}

impl UntypedValue {
    /// Create a new `CValue::Type(..)`.
    pub fn typ(type_: Type) -> UntypedValue {
        UntypedValue::Typed(CValue::Type(type_))
    }
}

impl From<CValue> for UntypedValue {
    fn from(value: CValue) -> Self {
        UntypedValue::Typed(value)
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
    orb: &'utir Orb,
    sink: DiagnosticSink,
    /// current item that we evaluate in.
    item: Opt<ItemId>,
    emit_diag: bool,
    /// location of the top most thing we try to evaluate
    loc: Span,
    /// Memoized results
    memo: HashMap<(ItemId, ExprId), UntypedValue>,
}

impl<'utir> UtirCtem<'utir> {
    /// Create a new UtirCtem with the orb and the sink.
    pub fn new(orb: &'utir Orb, sink: DiagnosticSink) -> UtirCtem<'utir> {
        UtirCtem {
            orb,
            sink,
            item: Opt::None,
            emit_diag: true,
            loc: Span::ZERO,
            memo: HashMap::new(),
        }
    }

    fn current_item(&self) -> &Item {
        self.orb.items.get(self.item.unwrap())
    }

    fn get_expr(&mut self, expr: ExprId) -> Expr {
        self.current_item().body().exprs.get(expr).clone()
    }

    fn get_expr_loc(&self, expr: ExprId) -> Option<Span> {
        self.current_item().body().expr_locs.get(expr).cloned()
    }

    fn get_expr_type(&self, expr: ExprId) -> Option<Uty> {
        self.current_item().body().expr_t.get(expr).copied()
    }

    /// Tries to evaluate the expression `expr` in the item `item`.
    ///
    /// # Errors
    ///
    /// If this function in unable to evaluate the expression at compile-time it
    /// will return `None` and maybe emit a diagnostic.
    pub fn evaluate_expr(&mut self, item: ItemId, expr: ExprId) -> Option<UntypedValue> {
        let old_item = self.item;
        let old_loc = mem::replace(&mut self.loc, Span::ZERO);

        self.item = Opt::Some(item);

        let expr_loc = self.get_expr_loc(expr).unwrap();

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
    pub fn evaluate_type(&mut self, item: ItemId, typ: ExprId) -> Option<Type> {
        let old_emit = self.emit_diag;
        self.emit_diag = false;

        let res = match self.evaluate_expr(item, typ) {
            Some(UntypedValue::Typed(CValue::Type(typ))) => Some(typ),
            Some(_) | None => None,
        };

        self.emit_diag = old_emit;

        res
    }

    /// Tries to evaluate the expression, return `None` if it can't evaluate at
    /// compile-time and NEVER emits a diagnostic.
    fn try_eval_expr(&mut self, expr: ExprId) -> Result<UntypedValue, (Span, Option<String>)> {
        self._eval_expr(expr)
    }

    /// Tries to evaluate the expression as a type, it it fails it returns the
    /// `void` type.
    fn try_eval_type(&mut self, expr: ExprId) -> Type {
        match self.try_eval_expr(expr) {
            Ok(UntypedValue::Typed(CValue::Type(typ))) => typ,
            Ok(_) => Type::PrimType(PrimType::Void),
            // NOTE: we don't emit a diag here because we will emit one in the
            // type-checking
            Err((loc, note)) => {
                self.sink.emit(CantEvaluateAtComptime {
                    note,
                    loc_expr: self.get_expr_loc(expr).unwrap(),
                    loc,
                });

                Type::PrimType(PrimType::Void)
            }
        }
    }

    fn _eval_expr(&mut self, id: ExprId) -> Result<UntypedValue, (Span, Option<String>)> {
        if let Some(res) = self.memo.get(&(self.item.unwrap(), id)) {
            return Ok(res.clone());
        }

        let expr_loc = self.get_expr_loc(id).unwrap_or_default();
        let expr_t = self.get_expr_type(id);

        let expr_t = if let Some(Uty::Expr(expr)) = expr_t
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
            Expr::Int(i) => match expr_t {
                Some(Type::PrimType(ptype)) => match ptype {
                    PrimType::I8 => Ok(CValue::I8(i as i8).into()),
                    PrimType::I16 => Ok(CValue::I16(i as i16).into()),
                    PrimType::I32 => Ok(CValue::I32(i as i32).into()),
                    PrimType::I64 => Ok(CValue::I64(i as i64).into()),
                    PrimType::I128 => Ok(CValue::I128(i as i128).into()),
                    PrimType::Isz => Ok(CValue::isz64(i as i64).into()),
                    PrimType::U8 => Ok(CValue::U8(i as u8).into()),
                    PrimType::U16 => Ok(CValue::U16(i as u16).into()),
                    PrimType::U32 => Ok(CValue::U32(i as u32).into()),
                    PrimType::U64 => Ok(CValue::U64(i as u64).into()),
                    PrimType::U128 => Ok(CValue::U128(i).into()),
                    PrimType::Usz => Ok(CValue::usz64(i as u64).into()),
                    _ => Ok(UntypedValue::Int(i)),
                },
                _ => Ok(UntypedValue::Int(i)),
            },
            Expr::Char(c) => Ok(CValue::Char(c).into()),
            Expr::Float(f) => match expr_t {
                Some(Type::PrimType(ptype)) => match ptype {
                    PrimType::F32 => Ok(CValue::F32(f.into_f64() as f32).into()),
                    PrimType::F64 => Ok(CValue::F64(f.into_f64()).into()),
                    _ => Ok(UntypedValue::Float(f.into_f64())),
                },
                _ => Ok(UntypedValue::Float(f.into_f64())),
            },
            Expr::Str(s) => Ok(CValue::Str(s.clone()).into()),
            Expr::CStr(s) => Ok(CValue::CStr(s.clone()).into()),
            Expr::Bool(b) => Ok(CValue::Bool(b).into()),
            Expr::PtrType(mutability, pointee) => {
                let pointee_t = self.try_eval_type(pointee);

                Ok(UntypedValue::typ(Type::Ptr(
                    mutability,
                    Box::new(pointee_t),
                )))
            }
            Expr::FunptrType(args, ret) => {
                let mut args_t = Vec::with_capacity(args.len());

                for arg in args {
                    args_t.push(self.try_eval_type(arg));
                }

                let ret_t = if let Some(ret) = ret.expand() {
                    self.try_eval_type(ret)
                } else {
                    Type::PrimType(PrimType::Void)
                };

                // NOTE: again no diag emitted, we will emit one in
                // type-checking.

                Ok(UntypedValue::typ(Type::FunPtr(args_t, Box::new(ret_t))))
            }
            Expr::PrimType(ptype) => Ok(UntypedValue::typ(Type::PrimType(ptype))),
            _ => Err((expr_loc, None)),
        }?;

        self.memo.insert((self.item.unwrap(), id), res.clone());

        Ok(res)
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
