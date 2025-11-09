//! Untyped Intermediate Representation of Lun, used to make type information
//! explicit so that compile-time evaluation and type-evaluation (a special case
//! of comptime eval) can easily work with types.

use std::{collections::HashMap, mem};

use lunc_ast::{BinOp, PrimType, UnOp};
use lunc_desugar::{
    DsBlock, DsDirective, DsExprKind, DsExpression, DsItem, DsModule, DsParam, DsStatement,
    DsStmtKind,
    symbol::{Symbol, SymbolKind},
};
use lunc_diag::{DiagnosticSink, feature_todo};
use lunc_entity::{EntityDb, EntitySet, Opt, OptionExt, SparseMap};
use lunc_token::{Lit, LitKind, LitVal};
use lunc_utils::{default, opt_unreachable};

use crate::{
    diags::{FunctionInGlobalMut, UnknownLitTag},
    utir::*,
};

pub mod diags;
pub mod pretty;
pub mod utir;

/// Constructs the [UTIR](utir) from [DSIR](lunc_desugar)
///
/// ## Population Stage
///
/// First pass on the DSIR, takes the global items and build a create it's
/// counterpart in UTIR, and adds mapping from `Symbol` to `DefId`.
///
/// Note that this stage only goes through the items but not their content, the
/// mapping of symbols defined inside of an item is mapped when the definition
/// is encountered, it causes no problem to do it like that because, items
/// defined inside need a forward definition.
#[derive(Debug, Clone)]
pub struct UtirGen {
    /// The generated orb
    orb: Orb,
    /// The symbol database, taken from the desugarrer, it's stored here to
    /// ensure symbols will remain alive until we finish the DSIR => UTIR.
    symdb: EntityDb<Symbol>,
    /// Symbol to AnyId mapping.
    sym_to_def: SparseMap<Symbol, DefId>,
    /// Diagnostic sink
    sink: DiagnosticSink,

    //
    // ITEM SPECIFIC
    //
    /// Current item being lowered.
    item: Opt<ItemId>,

    //
    // BODY SPECIFIC
    //
    /// A mapping of the primitive type to the expr.
    ///
    /// The thing is that when we build `Expr::PrimType`s we quickly have
    /// a bunch of them, this hash map is here so that we can re-use those
    /// type-expression instead of having 10,000 of them.
    types_exprs: HashMap<PrimType, ExprId>,

    //
    // FUNDEF SPECIFIC
    //
    /// Return type of the current function.
    fun_ret_ty: Opt<ExprId>,
}

impl UtirGen {
    /// Create a new utir-generator
    pub fn new(symdb: EntityDb<Symbol>, sink: DiagnosticSink) -> UtirGen {
        UtirGen {
            orb: Orb::default(),
            symdb,
            sym_to_def: SparseMap::new(),
            sink,
            item: Opt::None,
            types_exprs: HashMap::new(),
            fun_ret_ty: Opt::None,
        }
    }

    /// Produce the [Orb] for the given DSIR.
    pub fn produce(&mut self, dsir: DsModule) -> Orb {
        assert!(dsir.fid.is_root(), "expected the root module.");

        self.populate_mod(&dsir);
        self.gen_module(&dsir);

        mem::take(&mut self.orb)
    }

    /// Populate a module, see [population stage] for more details.
    ///
    /// [population stage]: UtirGen#population-stage
    pub fn populate_mod(&mut self, module: &DsModule) {
        self.populate_items(&module.items);
    }

    fn populate_items(&mut self, items: &[DsItem]) {
        for item in items {
            self.populate_item(item);
        }
    }

    fn clear_fundef_specific(&mut self) {
        self.fun_ret_ty = Opt::None;
    }

    fn clear_item_specific(&mut self) {
        self.item = Opt::None;
    }

    fn clear_body_specific(&mut self) {
        self.types_exprs.clear();
    }

    /// Maps a symbol to a defid
    pub fn map_sym_to_def(&mut self, sym: Symbol, def: DefId) {
        self.sym_to_def.insert(sym, def);
    }

    /// Get an item from the `Sym -> Def` mapping
    pub fn get_item(&mut self, sym: Symbol) -> ItemId {
        match self.sym_to_def.get(sym) {
            Some(DefId::ItemId(id)) => *id,
            Some(_) => panic!("symbol is not mapped to an item"),
            None => panic!("symbol is not mapped"),
        }
    }

    /// Populate an item, see [population stage] for more details.
    ///
    /// [population stage]: UtirGen#population-stage
    pub fn populate_item(&mut self, item: &DsItem) {
        match item {
            DsItem::GlobalDef {
                name,
                mutability: _,
                typeexpr: _,
                value,
                loc,
                sym,
            } if value.is_fundef() => {
                let id = self.orb.items.create(Item::Fundef(Fundef {
                    name: name.clone(),
                    loc: loc.clone().unwrap(),
                    ..default()
                }));

                self.map_sym_to_def(sym.unwrap_sym(), DefId::ItemId(id));
            }
            DsItem::GlobalDef {
                name,
                mutability: _,
                typeexpr: _,
                value,
                loc,
                sym,
            } if value.is_fundecl() => {
                let id = self.orb.items.create(Item::Fundecl(Fundecl {
                    name: name.clone(),
                    loc: loc.clone().unwrap(),
                    ..default()
                }));

                self.map_sym_to_def(sym.unwrap_sym(), DefId::ItemId(id));
            }
            DsItem::GlobalDef {
                name,
                mutability: _,
                typeexpr: _,
                value: _,
                loc,
                sym,
            } => {
                let id = self.orb.items.create(Item::GlobalDef(GlobalDef {
                    name: name.clone(),
                    loc: loc.clone().unwrap(),
                    ..default()
                }));

                self.map_sym_to_def(sym.unwrap_sym(), DefId::ItemId(id));
            }
            DsItem::GlobalUninit {
                name,
                typeexpr: _,
                loc,
                sym,
            } => {
                let id = self.orb.items.create(Item::GlobalUninit(GlobalUninit {
                    name: name.clone(),
                    loc: loc.clone().unwrap(),
                    ..default()
                }));

                self.map_sym_to_def(sym.unwrap_sym(), DefId::ItemId(id));
            }
            DsItem::Module {
                name,
                module,
                loc,
                sym,
            } => {
                let id = self.orb.items.create(Item::Module(Module {
                    name: name.clone(),
                    loc: loc.clone().unwrap(),
                    ..default()
                }));

                self.map_sym_to_def(sym.unwrap_sym(), DefId::ItemId(id));

                self.populate_mod(module);
            }
            DsItem::ExternBlock { items, .. } => {
                self.populate_items(items);
            }
            DsItem::Directive(DsDirective::Import { .. }) => {
                // we do nothing import is removed after DSIR => UTIR conversion
            }
            DsItem::Directive(DsDirective::Mod { .. }) => {
                // SAFETY: it was removed by the desugarrer
                opt_unreachable!("should've been removed by the desugarrer")
            }
        }
    }

    /// Returns the content of the current item.
    fn item_mut(&mut self) -> &mut Item {
        let id = self.item.expand().expect("No current item");

        self.orb.items.get_mut(id)
    }

    /// Returns a mutable ref to the body of the current item.
    #[inline(always)]
    fn body(&mut self) -> &mut Body {
        self.item_mut().body_mut()
    }

    /// Returns the current fundef.
    fn fundef_mut(&mut self) -> &mut Fundef {
        if let Item::Fundef(fundef) = self.item_mut() {
            fundef
        } else {
            panic!("the current item isn't a fundef")
        }
    }

    /// Creates a `Expr::PrimType(ptype)` in the current body and returns it.
    fn ptype_expr(&mut self, ptype: PrimType) -> ExprId {
        self.types_exprs.get(&ptype).copied().unwrap_or_else(|| {
            let ptype_e = self.body().exprs.create(Expr::PrimType(ptype));

            self.types_exprs.insert(ptype, ptype_e);

            ptype_e
        })
    }

    /// Generate the UTIR for a given module.
    pub fn gen_module(&mut self, module: &DsModule) {
        for item in &module.items {
            self.gen_item(item);
        }
    }

    fn gen_item(&mut self, item: &DsItem) -> Option<ItemId> {
        let item = match item {
            DsItem::GlobalDef {
                name: _,
                mutability,
                typeexpr,
                value,
                loc,
                sym,
            } if value.is_fundef() => {
                if mutability.is_mut() {
                    self.sink.emit(FunctionInGlobalMut {
                        fun: FunctionInGlobalMut::FUNDEF,
                        loc: loc.clone().unwrap(),
                    });
                }

                let DsExprKind::FunDefinition {
                    params,
                    rettypeexpr,
                    body: body_b,
                } = &value.expr
                else {
                    // SAFETY: already checked
                    opt_unreachable!()
                };

                let id = self.get_item(sym.unwrap_sym());
                self.item = Opt::Some(id);

                self.fundef_mut().typ = self.gen_option_expr(typeexpr, None);

                self.fundef_mut().params = self.gen_params(params)?;

                let type_e = self.ptype_expr(PrimType::Type);
                let ret_ty = self.gen_option_expr(rettypeexpr.as_deref(), ExtExpr::local(type_e));
                self.fundef_mut().ret_ty = ret_ty;
                self.fun_ret_ty = ret_ty;

                self.fundef_mut().entry =
                    self.gen_block(body_b, self.fun_ret_ty.map(ExtExpr::local));

                self.item = Opt::None;

                self.clear_fundef_specific();

                Some(id)
            }
            _ => todo!(),
        };

        self.clear_body_specific();
        self.clear_item_specific();

        item
    }

    fn gen_option_expr<'utir, 'dsir: 'utir>(
        &'utir mut self,
        expr: impl Into<Option<&'dsir DsExpression>>,
        typ: impl Into<Option<ExtExpr>>,
    ) -> Opt<ExprId> {
        expr.into().and_then(|e| self.gen_expr(e, typ)).shorten()
    }

    fn gen_expr(
        &mut self,
        expression: &DsExpression,
        typ: impl Into<Option<ExtExpr>>,
    ) -> Option<ExprId> {
        let expr = match &expression.expr {
            DsExprKind::Lit(Lit { kind, value, tag }) => match kind {
                LitKind::Char => {
                    if let Some(tag) = tag {
                        self.sink.emit(UnknownLitTag {
                            kind: kind.clone(),
                            tag: tag.to_string(),
                            loc: expression.loc.clone().unwrap(),
                        });
                    }

                    let LitVal::Char(char) = value else {
                        // SAFETY: guaranteed by Lit.
                        opt_unreachable!()
                    };

                    Expr::Char(*char)
                }
                LitKind::Integer => {
                    let ptype = match tag.as_deref() {
                        Some("isz") => Some(PrimType::Isz),
                        Some("i128") => Some(PrimType::I128),
                        Some("i64") => Some(PrimType::I64),
                        Some("i32") => Some(PrimType::I32),
                        Some("i16") => Some(PrimType::I16),
                        Some("i8") => Some(PrimType::I8),
                        Some("usz") => Some(PrimType::Usz),
                        Some("u128") => Some(PrimType::U128),
                        Some("u64") => Some(PrimType::U64),
                        Some("u32") => Some(PrimType::U32),
                        Some("u16") => Some(PrimType::U16),
                        Some("u8") => Some(PrimType::U8),
                        Some(tag) => {
                            self.sink.emit(UnknownLitTag {
                                kind: kind.clone(),
                                tag: tag.to_string(),
                                loc: expression.loc.clone().unwrap(),
                            });

                            None
                        }
                        None => None,
                    };

                    let LitVal::Int(int) = value else {
                        // SAFETY: guaranteed by Lit.
                        opt_unreachable!()
                    };

                    let expr = Expr::Int(*int);
                    if let Some(ptype) = ptype {
                        let val = self.body().exprs.create(expr);
                        let type_e = self.ptype_expr(ptype);

                        Expr::Typed {
                            typ: ExtExpr::local(type_e),
                            val,
                        }
                    } else {
                        expr
                    }
                }
                LitKind::Float => {
                    let ptype = match tag.as_deref() {
                        Some("f64") => Some(PrimType::F64),
                        Some("f32") => Some(PrimType::F32),
                        Some(tag) => {
                            self.sink.emit(UnknownLitTag {
                                kind: kind.clone(),
                                tag: tag.to_string(),
                                loc: expression.loc.clone().unwrap(),
                            });

                            None
                        }
                        None => None,
                    };

                    let LitVal::Float(float) = value else {
                        // SAFETY: guaranteed by Lit.
                        opt_unreachable!()
                    };

                    let expr = Expr::Float(*float);
                    if let Some(ptype) = ptype {
                        let val = self.body().exprs.create(expr);
                        let type_e = self.ptype_expr(ptype);

                        Expr::Typed {
                            typ: ExtExpr::local(type_e),
                            val,
                        }
                    } else {
                        expr
                    }
                }
                LitKind::Str => {
                    if let Some(tag) = tag {
                        self.sink.emit(UnknownLitTag {
                            kind: kind.clone(),
                            tag: tag.to_string(),
                            loc: expression.loc.clone().unwrap(),
                        });
                    }

                    let LitVal::Str(str) = value else {
                        // SAFETY: guaranteed by Lit.
                        opt_unreachable!()
                    };

                    Expr::Str(str.clone().into_boxed_str())
                }
                LitKind::CStr => {
                    debug_assert!(tag.is_none(), "cstr's tag is always none.");

                    let LitVal::Str(cstr) = value else {
                        // SAFETY: guaranteed by Lit.
                        opt_unreachable!()
                    };

                    Expr::CStr(cstr.clone().into_boxed_str())
                }
            },
            DsExprKind::BoolLit(b) => Expr::Bool(*b),
            DsExprKind::Path(lazy) => {
                let symref = lazy.unwrap_sym();
                let sym = self.symdb.get(symref);

                if sym.kind == SymbolKind::PrimitiveType {
                    let ptype = match sym.name.as_str() {
                        "isz" => PrimType::Isz,
                        "i128" => PrimType::I128,
                        "i64" => PrimType::I64,
                        "i32" => PrimType::I32,
                        "i16" => PrimType::I16,
                        "i8" => PrimType::I8,
                        "usz" => PrimType::Usz,
                        "u128" => PrimType::U128,
                        "u64" => PrimType::U64,
                        "u32" => PrimType::U32,
                        "u16" => PrimType::U16,
                        "u8" => PrimType::U8,
                        "f128" => PrimType::F128,
                        "f64" => PrimType::F64,
                        "f32" => PrimType::F32,
                        "f16" => PrimType::F16,
                        "bool" => PrimType::Bool,
                        "str" => PrimType::Str,
                        "char" => PrimType::Char,
                        "never" => PrimType::Never,
                        "void" => PrimType::Void,
                        "type" => PrimType::Type,
                        ptype => panic!("unknown primitive type {ptype:?}"),
                    };

                    // NOTE: here we don't use self.ptype_expr(..) because we
                    // want to keep the location of this primitive type.
                    Expr::PrimType(ptype)
                } else if let Some(defid) = self.sym_to_def.get(symref) {
                    match defid {
                        DefId::ParamId(param) => Expr::Param(*param),
                        DefId::BindingId(binding) => Expr::Binding(*binding),
                        DefId::ItemId(item) => Expr::Item(*item),
                    }
                } else {
                    // SAFETY: all symbols used in DSIR are mapped.
                    opt_unreachable!("unknown symbol")
                }
            }
            DsExprKind::Binary {
                lhs,
                op: BinOp::Assignment,
                rhs,
            } if lhs.is_underscore() => return self.gen_expr(rhs, None),
            DsExprKind::Binary { lhs, op, rhs } => {
                let lhs = self.gen_expr(lhs, None)?;
                let rhs = self.gen_expr(rhs, None)?;

                let expr = Expr::Binary(lhs, op.clone(), rhs);
                if op.is_relational() || op.is_logical() {
                    Expr::Typed {
                        typ: ExtExpr::local(self.ptype_expr(PrimType::Bool)),
                        val: self.body().exprs.create(expr),
                    }
                } else {
                    expr
                }
            }
            DsExprKind::Unary { op, expr } => {
                let expr = self.gen_expr(expr, None)?;

                let expr = Expr::Unary(op.clone(), expr);

                if *op == UnOp::Not {
                    Expr::Typed {
                        typ: ExtExpr::local(self.ptype_expr(PrimType::Bool)),
                        val: self.body().exprs.create(expr),
                    }
                } else {
                    expr
                }
            }
            DsExprKind::Borrow(mutability, expr) => {
                let expr = self.gen_expr(expr, None)?;

                Expr::Borrow(*mutability, expr)
            }
            DsExprKind::Call { callee, args } => {
                let callee = self.gen_expr(callee, None)?;
                let mut args_e = Vec::with_capacity(args.len());

                for arg in args {
                    if let Some(arg) = self.gen_expr(arg, None) {
                        args_e.push(arg);
                    }
                }

                Expr::Call {
                    callee,
                    args: args_e,
                }
            }
            DsExprKind::If {
                cond,
                then_br,
                else_br,
            } => {
                let cond = self.gen_expr(cond, None)?;

                let bool_e = self.ptype_expr(PrimType::Bool);
                let typed_cond = self.body().exprs.create(Expr::Typed {
                    typ: ExtExpr::local(bool_e),
                    val: cond,
                });

                let then_e = self.gen_expr(then_br, None)?;
                let else_e = self.gen_option_expr(else_br.as_deref(), None);

                Expr::If {
                    cond: typed_cond,
                    then_e,
                    else_e,
                }
            }
            DsExprKind::Block { label, block } => {
                assert!(label.is_none(), "LABELS NOT YET IMPLEMENTED");

                let block = self.gen_block(block, None);

                Expr::Block(Opt::None, block)
            }
            DsExprKind::Loop { label, body } => {
                assert!(label.is_none(), "LABELS NOT YET IMPLEMENTED");
                let void_e = self.ptype_expr(PrimType::Void);
                let body = self.gen_block(body, ExtExpr::local(void_e));

                Expr::Loop(Opt::None, body)
            }
            DsExprKind::Return { expr } => {
                let expr =
                    self.gen_option_expr(expr.as_deref(), self.fun_ret_ty.map(ExtExpr::local));

                Expr::Return(expr)
            }
            DsExprKind::Break { label, expr } => {
                assert!(label.is_none(), "LABELS NOT YET IMPLEMENTED");

                let expr = self.gen_option_expr(expr.as_deref(), None);

                Expr::Break(Opt::None, expr)
            }
            DsExprKind::Continue { label } => {
                assert!(label.is_none(), "LABELS NOT YET IMPLEMENTED");

                Expr::Continue(Opt::None)
            }
            DsExprKind::Null => {
                self.sink.emit(feature_todo! {
                    feature: "null expr",
                    label: "field access and struct type definition",
                    loc: expression.loc.clone().unwrap()
                });

                return None;
            }
            DsExprKind::Field { .. } => {
                self.sink.emit(feature_todo! {
                    feature: "field expr",
                    label: "field access and struct type definition",
                    loc: expression.loc.clone().unwrap()
                });

                return None;
            }
            DsExprKind::Underscore => {
                // SAFETY: we never call `gen_expr` on an underscore, because we
                // handle the case of a `_ = EXPR` before.
                opt_unreachable!();
            }
            DsExprKind::FunDefinition { .. } => {
                self.sink.emit(feature_todo! {
                    feature: "local fundef",
                    label: "fundefs inside an expression isn't supported",
                    loc: expression.loc.clone().unwrap(),
                });

                return None;
            }
            DsExprKind::FunDeclaration { .. } => {
                self.sink.emit(feature_todo! {
                    feature: "local fundecl",
                    label: "fundefs inside an expression isn't supported",
                    loc: expression.loc.clone().unwrap(),
                });

                return None;
            }
            DsExprKind::PointerType(mutability, pointee) => {
                let type_e = self.ptype_expr(PrimType::Type);
                let pointee = self.gen_expr(pointee, ExtExpr::local(type_e))?;

                Expr::PtrType(*mutability, pointee)
            }
            DsExprKind::FunPtrType { args: ds_args, ret } => {
                let mut args = Vec::with_capacity(ds_args.len());

                let type_e = self.ptype_expr(PrimType::Type);
                for arg in ds_args {
                    if let Some(arg) = self.gen_expr(arg, ExtExpr::local(type_e)) {
                        args.push(arg)
                    }
                }

                let ret = self.gen_option_expr(ret.as_deref(), ExtExpr::local(type_e));

                Expr::FunptrType(args, ret)
            }
            DsExprKind::Poisoned { diag } => {
                debug_assert!(diag.is_none());

                return None;
            }
        };

        let id = self.body().exprs.create(expr);

        if let Some(ref loc) = expression.loc {
            self.body().expr_locs.insert(id, loc.clone());
        }

        if let Some(typ) = typ.into() {
            Some(self.body().exprs.create(Expr::Typed { typ, val: id }))
        } else {
            Some(id)
        }
    }

    fn gen_stmt(&mut self, stmt: &DsStatement) -> Option<StmtId> {
        let s = match &stmt.stmt {
            DsStmtKind::BindingDef {
                name,
                mutability,
                typeexpr,
                value,
                sym,
            } => {
                let type_e = self.ptype_expr(PrimType::Type);
                let typ = self.gen_option_expr(typeexpr, Some(ExtExpr::local(type_e)));
                let val = self.gen_expr(value, typ.expand().map(ExtExpr::local))?;

                let bind = self.body().bindings.create(BindingDef {
                    name: name.clone(),
                    mutability: *mutability,
                    typ,
                    val,
                });

                self.map_sym_to_def(sym.unwrap_sym(), DefId::BindingId(bind));

                self.body().stmts.create(Stmt::BindingDef(bind))
            }
            DsStmtKind::Defer { expr: _ } => {
                self.sink.emit(feature_todo! {
                    feature: "defer statement",
                    label: "field access and struct type definition",
                    loc: stmt.loc.clone().unwrap()
                });

                return None;
            }
            DsStmtKind::Expression(expr) => {
                let e = self.gen_expr(expr, None)?;

                self.body().stmts.create(Stmt::Expression(e))
            }
        };

        if let Some(ref loc) = stmt.loc {
            self.body().stmt_locs.insert(s, loc.clone());
        }

        Some(s)
    }

    fn gen_params(&mut self, params: &[DsParam]) -> Option<EntityDb<ParamId>> {
        let mut params_db = EntityDb::new();

        let type_e = self.ptype_expr(PrimType::Type);

        for DsParam {
            name,
            typeexpr,
            loc,
            sym,
        } in params
        {
            let param = params_db.create(Param {
                name: name.clone(),
                typ: self.gen_expr(typeexpr, ExtExpr::local(type_e))?,
                loc: loc.clone().unwrap(),
            });

            self.map_sym_to_def(sym.unwrap_sym(), DefId::ParamId(param));
        }

        Some(params_db)
    }

    /// Generate the UTIR for a DSIR block.
    ///
    /// It will make the tail be `typed(typ, tail)` if a `typ` is provided.
    fn gen_block(&mut self, block: &DsBlock, typ: impl Into<Option<ExtExpr>>) -> BlockId {
        let DsBlock {
            stmts,
            last_expr,
            loc,
        } = block;

        let mut stmts_set = EntitySet::new();

        for stmt in stmts {
            if let Some(s) = self.gen_stmt(stmt) {
                stmts_set.insert(s)
            }
        }

        let tail = self.gen_option_expr(last_expr.as_deref(), typ);

        self.body().blocks.create(Block {
            stmts: stmts_set,
            tail,
            loc: loc.clone().unwrap(),
        })
    }
}
