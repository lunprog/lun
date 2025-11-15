//! Untyped Intermediate Representation of Lun, used to make type information
//! explicit so that compile-time evaluation and type-evaluation (a special case
//! of comptime eval) can easily work with types.

use std::{collections::HashMap, mem};

use lunc_ast::{BinOp, ItemContainer, ItemKind, Mutability, PrimType, Spanned, UnOp};
use lunc_desugar::{
    DsBlock, DsDirective, DsExprKind, DsExpression, DsItem, DsModule, DsParam, DsStatement,
    DsStmtKind,
    symbol::{Symbol, SymbolKind},
};
use lunc_diag::{DiagnosticSink, feature_todo};
use lunc_entity::{Entity, EntityDb, EntitySet, Opt, OptionExt, SparseMap};
use lunc_token::{Lit, LitKind, LitVal};
use lunc_utils::{Span, default, opt_unreachable};

use crate::{
    diags::{
        BreakUseAnImplicitLabelInBlock, BreakWithValueUnsupported, CantContinueABlock,
        FunctionInGlobalMut, ItemNotAllowedInExternBlock, LabelKwOutsideLoopOrBlock,
        OutsideExternBlock, UnknownLitTag, UseOfUndefinedLabel,
    },
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
///
/// ## Generation Stage
///
/// It's the stage where we actually lower the majority of the DSIR to UTIR,
/// while lowering we try to add as much information on types as possible with
/// the following rules:
/// - *Is the type trivially known?* Like tagged integer literals (`12'u8` has
///   type `u8`), so here we assign the expression a `Uty::Expr`.
/// - *Is the type unknown? Or is it hard to infer?* Like untagged integer
///   literals, `12` can have type `u8`, `i8`, `usz`, `i32` etc etc.. Or a
///   user-binding that doesn't have an explicit type. Here we assign the
///   expression to a new type-variable.
/// - *Can the type be easily inferred?* Like binary expression, calls, etc..
///   Here the type is really not that complex for the type-checker to guess so
///   we don't assign a type to it *NOW*. **Why?** because it may make things
///   harder than they really are.
///
/// So the rule is simple, we try not to use too much type-variables.
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
    item_kind: ItemKind,

    //
    // ITEM CONTAINER SPECIFIC
    //
    container: ItemContainer,
    extern_block_loc: Option<Span>,

    //
    // BODY SPECIFIC
    //
    /// A mapping of the primitive type to the expr.
    ///
    /// The thing is that when we build `Expr::PrimType`s we quickly have
    /// a bunch of them, this hash map is here so that we can re-use those
    /// type-expression instead of having 10,000 of them.
    types_exprs: HashMap<PrimType, ExprId>,
    /// A stack of the current labels
    label_stack: Vec<LabelId>,

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
            item_kind: ItemKind::Fundef,
            container: ItemContainer::Module,
            extern_block_loc: None,
            types_exprs: HashMap::new(),
            label_stack: Vec::new(),
            fun_ret_ty: Opt::None,
        }
    }

    /// Produce the [Orb] for the given DSIR.
    pub fn produce(&mut self, mut dsir: DsModule) -> Orb {
        assert!(dsir.fid.is_root(), "expected the root module.");

        self.populate_mod(&mut dsir);
        self.gen_module(&dsir);

        mem::take(&mut self.orb)
    }

    /// Populate a module, see [population stage] for more details.
    ///
    /// [population stage]: UtirGen#population-stage
    pub fn populate_mod(&mut self, module: &mut DsModule) {
        self.populate_items(&mut module.items);
    }

    fn populate_items(&mut self, items: &mut [DsItem]) {
        for item in items {
            self.populate_item(item);
        }
    }

    fn clear_fundef_specific(&mut self) {
        self.fun_ret_ty = Opt::None;
    }

    fn clear_item_specific(&mut self) {
        self.item = Opt::None;
        self.extern_block_loc = None;
    }

    fn clear_body_specific(&mut self) {
        self.types_exprs.clear();
        self.label_stack.clear();
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
    pub fn populate_item(&mut self, item: &mut DsItem) {
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
                mutability,
                typeexpr: _,
                value: _,
                loc,
                sym,
            } => {
                let id = self.orb.items.create(Item::GlobalDef(GlobalDef {
                    name: name.clone(),
                    mutability: *mutability,
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
            DsItem::ExternBlock {
                abi,
                items,
                loc,
                id,
            } => {
                self.populate_items(items);

                let item_id = self.orb.items.create(Item::ExternBlock(ExternBlock {
                    abi: *abi,
                    items: EntitySet::new(),
                    loc: loc.clone().unwrap(),
                }));

                *id = Some(item_id.to_any());
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
    #[track_caller]
    fn item_mut(&mut self) -> &mut Item {
        let id = self.item.expand().expect("No current item");

        self.orb.items.get_mut(id)
    }

    fn item(&self) -> &Item {
        let id = self.item.expand().expect("No current item");

        self.orb.items.get(id)
    }

    /// Returns a mutable ref to the body of the current item.
    #[inline(always)]
    fn body(&mut self) -> &mut Body {
        self.item_mut().body_mut()
    }

    fn body_ref(&self) -> &Body {
        self.item().body()
    }

    fn extern_block_loc(&self) -> Span {
        self.extern_block_loc.clone().unwrap()
    }

    /// Returns the current fundef.
    fn fundef_mut(&mut self) -> &mut Fundef {
        if let Item::Fundef(fundef) = self.item_mut() {
            fundef
        } else {
            opt_unreachable!("the current item isn't a fundef")
        }
    }

    /// Returns the current fundecl.
    fn fundecl_mut(&mut self) -> &mut Fundecl {
        if let Item::Fundecl(fundecl) = self.item_mut() {
            fundecl
        } else {
            opt_unreachable!("the current item isn't a fundecl")
        }
    }

    /// Returns the current globaldef.
    fn globaldef_mut(&mut self) -> &mut GlobalDef {
        if let Item::GlobalDef(globaldef) = self.item_mut() {
            globaldef
        } else {
            // SAFETY: upheld by caller
            opt_unreachable!("the current item isn't a globaldef")
        }
    }

    /// Returns the current global_uninit.
    fn global_uninit_mut(&mut self) -> &mut GlobalUninit {
        if let Item::GlobalUninit(global_uninit) = self.item_mut() {
            global_uninit
        } else {
            // SAFETY: upheld by caller
            opt_unreachable!("the current item isn't a global_uninit")
        }
    }

    /// Returns the current module.
    fn module_mut(&mut self) -> &mut Module {
        if let Item::Module(module) = self.item_mut() {
            module
        } else {
            // SAFETY: upheld by caller
            opt_unreachable!("the current item isn't a module")
        }
    }

    /// Returns the current extern_block.
    fn extern_block_mut(&mut self) -> &mut ExternBlock {
        if let Item::ExternBlock(extern_block) = self.item_mut() {
            extern_block
        } else {
            // SAFETY: upheld by caller
            opt_unreachable!("the current item isn't a extern_block")
        }
    }

    /// Creates a `Expr::PrimType(ptype)` in the current body and returns it.
    fn ptype_expr(&mut self, ptype: PrimType) -> ExprId {
        self.types_exprs.get(&ptype).copied().unwrap_or_else(|| {
            let ptype_e = self.body().exprs.create(Expr::PrimType(ptype));

            self.types_exprs.insert(ptype, ptype_e);

            let type_e = self.ptype_expr(PrimType::Type);
            self.body().expr_t.insert(ptype_e, Uty::Expr(type_e));

            ptype_e
        })
    }

    /// Push a constraint (`Con`) on `ty` if it is a `Some(Uty::TyVar(..))`.
    fn push_con(&mut self, ty: impl Into<Uty>, con: impl FnOnce(TyVar) -> Con) {
        if let Uty::TyVar(tyvar) = ty.into() {
            self.body().constraints.0.push(con(tyvar))
        }
    }

    fn expr_typ(&self, expr: impl Into<Option<ExprId>>) -> Option<Uty> {
        self.body_ref().expr_t.get(expr.into()?).copied()
    }

    /// Generate the UTIR for a given module.
    pub fn gen_module(&mut self, module: &DsModule) -> EntitySet<ItemId> {
        self.gen_items_in(&module.items, ItemContainer::Module)
    }

    /// Generate the UTIR for a given list of items and the item container.
    pub fn gen_items_in(
        &mut self,
        items: &[DsItem],
        container: ItemContainer,
    ) -> EntitySet<ItemId> {
        let old = self.container.clone();
        self.container = container;

        let mut itemset = EntitySet::new();

        for item in items {
            if let Some(id) = self.gen_item(item) {
                itemset.insert(id);
            }
        }

        self.container = old;

        itemset
    }

    /// Checks that the item kind is compatible inside of the item container
    fn check_item_container(&mut self, loc: Span) {
        match self.container {
            ItemContainer::Module => match self.item_kind {
                ItemKind::Fundef
                | ItemKind::GlobalDef
                | ItemKind::Module
                | ItemKind::ExternBlock
                | ItemKind::Directive => {}
                ItemKind::Fundecl => {
                    self.sink.emit(OutsideExternBlock {
                        item_name: diags::FUNDECL,
                        loc,
                    });
                }
                ItemKind::GlobalUninit => {
                    self.sink.emit(OutsideExternBlock {
                        item_name: diags::GLOBAL_UNINIT,
                        loc,
                    });
                }
            },
            ItemContainer::ExternBlock => match self.item_kind {
                ItemKind::Fundecl | ItemKind::GlobalUninit => {}
                ItemKind::Fundef => {
                    self.sink.emit(ItemNotAllowedInExternBlock {
                        item: diags::FUNDEF,
                        note: None,
                        loc,
                        extern_block_loc: self.extern_block_loc(),
                    });
                }
                ItemKind::GlobalDef => {
                    self.sink.emit(ItemNotAllowedInExternBlock {
                        item: diags::GLOBAL_DEF,
                        note: None,
                        loc,
                        extern_block_loc: self.extern_block_loc(),
                    });
                }
                ItemKind::Module => {
                    self.sink.emit(ItemNotAllowedInExternBlock {
                        item: diags::MODULE,
                        note: None,
                        loc,
                        extern_block_loc: self.extern_block_loc(),
                    });
                }
                ItemKind::ExternBlock => {
                    self.sink.emit(ItemNotAllowedInExternBlock {
                        item: diags::EXTERN_BLOCK,
                        note: Some("you probably want to un nest the extern block"),
                        loc,
                        extern_block_loc: self.extern_block_loc(),
                    });
                }
                ItemKind::Directive => {
                    self.sink.emit(ItemNotAllowedInExternBlock {
                        item: diags::DIRECTIVE,
                        note: None,
                        loc,
                        extern_block_loc: self.extern_block_loc(),
                    });
                }
            },
        }
    }

    fn gen_item(&mut self, item: &DsItem) -> Option<ItemId> {
        let loc = item.loc();
        self.item_kind = item.kind();

        self.check_item_container(loc);

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
                        fun: diags::FUNDEF,
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

                self.fundef_mut().typ = self.gen_option_expr(typeexpr);

                self.fundef_mut().params = self.gen_params(params)?;

                let ret_ty = self.gen_option_expr(rettypeexpr.as_deref());

                self.fundef_mut().ret_ty = ret_ty;
                self.fun_ret_ty = ret_ty;

                let entry = self.gen_block(body_b);

                // add the type constraint on the block if it's a typevar.
                let entry_t = self.body().blocks.get(entry).typ;
                if let Some(ret_ty) = self.fun_ret_ty.expand() {
                    self.push_con(entry_t, |tyvar| Con::Uty(tyvar, Uty::Expr(ret_ty)));
                }

                self.fundef_mut().entry = entry;

                self.item = Opt::None;

                self.clear_fundef_specific();

                Some(id)
            }
            DsItem::GlobalDef {
                name: _,
                mutability,
                typeexpr,
                value,
                loc,
                sym,
            } if value.is_fundecl() => {
                if mutability.is_mut() {
                    self.sink.emit(FunctionInGlobalMut {
                        fun: diags::FUNDECL,
                        loc: loc.clone().unwrap(),
                    });
                }

                let DsExprKind::FunDeclaration { args, rettypeexpr } = &value.expr else {
                    // SAFETY: already checked
                    opt_unreachable!()
                };

                let id = self.get_item(sym.unwrap_sym());
                self.item = Opt::Some(id);

                self.fundecl_mut().typ = self.gen_option_expr(typeexpr);

                for arg in args {
                    if let Some(expr) = self.gen_expr(arg) {
                        self.fundecl_mut().params.push(expr)
                    }
                }

                let ret_ty = self.gen_option_expr(rettypeexpr.as_deref());

                self.fundecl_mut().ret_ty = ret_ty;

                self.item = Opt::None;

                Some(id)
            }
            DsItem::GlobalDef {
                name: _,
                mutability: _,
                typeexpr,
                value,
                loc: _,
                sym,
            } => {
                let id = self.get_item(sym.unwrap_sym());
                self.item = Opt::Some(id);

                self.globaldef_mut().typ = self.gen_option_expr(typeexpr);

                self.globaldef_mut().value = self.gen_expr(value)?;

                Some(id)
            }
            DsItem::GlobalUninit {
                name: _,
                typeexpr,
                loc: _,
                sym,
            } => {
                let id = self.get_item(sym.unwrap_sym());
                self.item = Opt::Some(id);

                self.global_uninit_mut().typ = self.gen_expr(typeexpr)?;

                Some(id)
            }
            DsItem::Module {
                name: _,
                module,
                loc: _,
                sym,
            } => {
                let id = self.get_item(sym.unwrap_sym());
                self.item = Opt::Some(id);

                self.module_mut().items = self.gen_module(module);

                Some(id)
            }
            DsItem::ExternBlock {
                abi: _,
                items,
                loc,
                id,
            } => {
                let id = id.unwrap().downcast::<ItemId>();

                self.extern_block_loc = loc.clone();

                let items = self.gen_items_in(items, ItemContainer::ExternBlock);

                self.item = Opt::Some(id);
                self.extern_block_mut().items = items;

                Some(id)
            }
            DsItem::Directive(DsDirective::Import { .. }) => {
                // we do nothing import is removed after DSIR => UTIR conversion
                None
            }
            DsItem::Directive(DsDirective::Mod { .. }) => {
                // SAFETY: it was removed by the desugarrer
                opt_unreachable!("should've been removed by the desugarrer")
            }
        };

        self.clear_body_specific();
        self.clear_item_specific();

        item
    }

    fn labels_mut(&mut self) -> &mut EntityDb<LabelId> {
        &mut self.item_mut().body_mut().labels
    }

    /// Define a new label and put it on top of the stack
    fn define_label(&mut self, name: Option<Spanned<String>>, kind: LabelKind) -> LabelId {
        let lab = self.labels_mut().create_with(|id| Label {
            id,
            name,
            typ: None,
            kind,
            break_out: false,
        });

        self.label_stack.push(lab);

        lab
    }

    fn get_label_by_id(&self, label: LabelId) -> &Label {
        if !self.label_stack.contains(&label) {
            panic!("try to access a label that is not in the current label stack")
        }

        self.body_ref().labels.get(label)
    }

    fn mut_label_by_id(&mut self, label: LabelId) -> &mut Label {
        if !self.label_stack.contains(&label) {
            panic!("try to access a label that is not in the current label stack")
        }

        self.body().labels.get_mut(label)
    }

    fn get_label_by_name(&self, needle: &str) -> Option<&Label> {
        for lab in self.label_stack.iter().rev() {
            let label = self.get_label_by_id(*lab);

            if let Some(Spanned {
                node: ref name,
                loc: _,
            }) = label.name
                && name == needle
            {
                return Some(label);
            }
        }

        None
    }

    fn label_breaked(&mut self, id: LabelId) {
        self.mut_label_by_id(id).break_out = true;
    }

    fn gen_option_expr<'utir, 'dsir: 'utir>(
        &'utir mut self,
        expr: impl Into<Option<&'dsir DsExpression>>,
    ) -> Opt<ExprId> {
        expr.into().and_then(|e| self.gen_expr(e)).shorten()
    }

    fn gen_expr(&mut self, expression: &DsExpression) -> Option<ExprId> {
        let typ: Option<Uty>;

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

                    typ = Some(Uty::Expr(self.ptype_expr(PrimType::Char)));

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
                        let type_e = self.ptype_expr(ptype);
                        typ = Some(Uty::Expr(type_e));
                    } else {
                        let tyvar = self.body().type_vars.create_default();
                        self.push_con(tyvar, |_| Con::Integer(tyvar));

                        typ = Some(Uty::TyVar(tyvar));
                    }

                    expr
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
                        let type_e = self.ptype_expr(ptype);

                        typ = Some(Uty::Expr(type_e));
                    } else {
                        let tyvar = self.body().type_vars.create_default();
                        self.push_con(tyvar, |_| Con::Float(tyvar));

                        typ = Some(Uty::TyVar(tyvar));
                    }

                    expr
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

                    let str_t = self.ptype_expr(PrimType::Str);

                    typ = Some(Uty::Expr(
                        self.body()
                            .exprs
                            .create(Expr::PtrType(Mutability::Not, str_t)),
                    ));

                    Expr::Str(str.clone().into_boxed_str())
                }
                LitKind::CStr => {
                    debug_assert!(tag.is_none(), "cstr's tag is always none.");

                    let LitVal::Str(cstr) = value else {
                        // SAFETY: guaranteed by Lit.
                        opt_unreachable!()
                    };

                    let c_char_t = self.ptype_expr(PrimType::I8);

                    typ = Some(Uty::Expr(
                        self.body()
                            .exprs
                            .create(Expr::PtrType(Mutability::Not, c_char_t)),
                    ));

                    Expr::CStr(cstr.clone().into_boxed_str())
                }
            },
            DsExprKind::BoolLit(b) => {
                typ = Some(Uty::Expr(self.ptype_expr(PrimType::Bool)));
                Expr::Bool(*b)
            }
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

                    typ = Some(Uty::Expr(self.ptype_expr(PrimType::Type)));

                    // NOTE: here we don't use self.ptype_expr(..) because we
                    // want to keep the location of this primitive type.
                    Expr::PrimType(ptype)
                } else if let Some(defid) = self.sym_to_def.get(symref).copied() {
                    match defid {
                        DefId::ParamId(param) => {
                            typ = Some(self.fundef_mut().params.get(param).typ);

                            Expr::Param(param)
                        }
                        DefId::BindingId(binding) => {
                            typ = Some(self.body().bindings.get(binding).typ);

                            Expr::Binding(binding)
                        }
                        DefId::ItemId(item) => {
                            // the type would require some sort of evaluation,
                            // so we can't assign a type right now.
                            typ = None;

                            Expr::Item(item)
                        }
                    }
                } else {
                    // SAFETY: all symbols used in DSIR are mapped.
                    opt_unreachable!("unknown symbol")
                }
            }
            DsExprKind::Binary { lhs, op, rhs } => {
                let lhs = self.gen_expr(lhs)?;
                let rhs = self.gen_expr(rhs)?;

                let expr = Expr::Binary(lhs, op.clone(), rhs);

                if op.is_relational() || op.is_logical() {
                    typ = Some(Uty::Expr(self.ptype_expr(PrimType::Bool)));
                } else if *op == BinOp::Assignment {
                    if let Some(lhs_t) = self.expr_typ(lhs)
                        && let Some(rhs_t) = self.expr_typ(rhs)
                    {
                        self.push_con(lhs_t, |tyvar| Con::Uty(tyvar, rhs_t));
                    }

                    typ = Some(Uty::Expr(self.ptype_expr(PrimType::Void)));
                } else {
                    let tyvar = self.body().type_vars.create_default();

                    if let Some(lhs_t) = self.expr_typ(lhs) {
                        self.push_con(Uty::TyVar(tyvar), |_| Con::Uty(tyvar, lhs_t));
                    }

                    if let Some(rhs_t) = self.expr_typ(rhs) {
                        self.push_con(Uty::TyVar(tyvar), |_| Con::Uty(tyvar, rhs_t));
                    }

                    typ = Some(Uty::TyVar(tyvar));
                }

                expr
            }
            DsExprKind::Unary { op, expr } => {
                let expr = self.gen_expr(expr)?;

                let expr = Expr::Unary(op.clone(), expr);

                if *op == UnOp::Not {
                    typ = Some(Uty::Expr(self.ptype_expr(PrimType::Bool)));
                } else {
                    typ = None;
                }

                expr
            }
            DsExprKind::Borrow(mutability, expr) => {
                let expr = self.gen_expr(expr)?;

                typ = None;

                Expr::Borrow(*mutability, expr)
            }
            DsExprKind::Call { callee, args } => {
                let callee = self.gen_expr(callee)?;
                let mut args_e = Vec::with_capacity(args.len());

                for arg in args {
                    if let Some(arg) = self.gen_expr(arg) {
                        args_e.push(arg);
                    }
                }

                typ = None;

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
                let cond = self.gen_expr(cond)?;

                if let Some(cond_t) = self.expr_typ(cond) {
                    let bool_e = self.ptype_expr(PrimType::Bool);
                    self.push_con(cond_t, |tyvar| Con::Uty(tyvar, Uty::Expr(bool_e)));
                }

                let then_e = self.gen_expr(then_br)?;
                let else_e = self.gen_option_expr(else_br.as_deref());

                if let Some(else_e) = else_e.expand() {
                    let tyvar = self.body().type_vars.create_default();

                    if let Some(then_t) = self.expr_typ(then_e) {
                        self.push_con(tyvar, |_| Con::Uty(tyvar, then_t));
                    }

                    if let Some(else_t) = self.expr_typ(else_e) {
                        self.push_con(tyvar, |_| Con::Uty(tyvar, else_t));
                    }

                    typ = Some(Uty::TyVar(tyvar));
                } else {
                    typ = Some(Uty::Expr(self.ptype_expr(PrimType::Void)));
                }

                Expr::If {
                    cond,
                    then_e,
                    else_e,
                }
            }
            DsExprKind::Block { label, block } => {
                let block = self.gen_block(block);

                if let Some(label) = label.clone() {
                    let lab = self.define_label(Some(label), LabelKind::Block);

                    typ = Some(
                        self.get_label_by_id(lab)
                            .typ
                            .unwrap_or_else(|| self.body_ref().blocks.get(block).typ),
                    );

                    Expr::Block(Opt::Some(lab), block)
                } else {
                    typ = Some(self.body_ref().blocks.get(block).typ);

                    Expr::Block(Opt::None, block)
                }
            }
            DsExprKind::Loop { label, body } => {
                let is_while = matches!(
                    body.stmts.first(),
                    Some(DsStatement {
                        stmt: DsStmtKind::Expression(DsExpression {
                            expr: DsExprKind::If { .. },
                            loc: None
                        }),
                        loc: None
                    })
                );

                let kind = if is_while {
                    LabelKind::PredicateLoop
                } else {
                    LabelKind::InfiniteLoop
                };

                let lab = self.define_label(label.clone(), kind);

                let void_e = self.ptype_expr(PrimType::Void);
                let body = self.gen_block(body);
                let body_t = self.body().blocks.get(body).typ;

                self.push_con(body_t, |tyvar| Con::Uty(tyvar, Uty::Expr(void_e)));

                let info = self.get_label_by_id(lab);

                typ = if !info.break_out {
                    Some(Uty::Expr(self.ptype_expr(PrimType::Never)))
                } else if let Some(typ) = info.typ {
                    Some(typ)
                } else {
                    Some(Uty::Expr(self.ptype_expr(PrimType::Void)))
                };

                self.label_stack.pop();

                Expr::Loop(lab, body)
            }
            DsExprKind::Return { expr } => {
                let expr = self.gen_option_expr(expr.as_deref());

                if let Some(ret_ty) = self.fun_ret_ty.expand()
                    && let Some(expr) = expr.expand()
                    && let Some(expr_t) = self.expr_typ(expr)
                {
                    self.push_con(expr_t, |tyvar| Con::Uty(tyvar, Uty::Expr(ret_ty)));
                }

                typ = Some(Uty::Expr(self.ptype_expr(PrimType::Never)));

                Expr::Return(expr)
            }
            DsExprKind::Break { label, expr } => {
                let (label_typ, label_kind, id) = if let Some(label) = label {
                    let Some(Label { id, typ, kind, .. }) = self.get_label_by_name(label) else {
                        self.sink.emit(UseOfUndefinedLabel {
                            name: label.clone(),
                            // TODO: add location of the label name
                            loc: expression.loc.clone().unwrap(),
                        });

                        return None;
                    };

                    (*typ, kind.clone(), *id)
                } else {
                    let Some(id) = self.label_stack.last() else {
                        self.sink.emit(LabelKwOutsideLoopOrBlock {
                            kw: diags::BREAK,
                            loc: expression.loc.clone().unwrap(),
                        });

                        return None;
                    };

                    let Label { typ, kind, .. } = self.get_label_by_id(*id).clone();

                    if !kind.is_loop() {
                        self.sink.emit(BreakUseAnImplicitLabelInBlock {
                            loc: expression.loc.clone().unwrap(),
                        });
                    }

                    (typ, kind, *id)
                };

                let expr = if let Some(expr) = expr {
                    let expr = self.gen_expr(expr)?;

                    if !label_kind.can_have_val() {
                        self.sink.emit(BreakWithValueUnsupported {
                            loc: expression.loc.clone().unwrap(),
                        });
                    } else if label_typ.is_none() {
                        self.mut_label_by_id(id).typ = if let Some(typ) = self.expr_typ(expr) {
                            Some(typ)
                        } else {
                            let tyvar = self.body().type_vars.create_default();

                            self.body().expr_t.insert(expr, Uty::TyVar(tyvar));

                            Some(Uty::TyVar(tyvar))
                        };
                    }

                    Opt::Some(expr)
                } else {
                    if label_typ.is_none() {
                        self.mut_label_by_id(id).typ =
                            Some(Uty::Expr(self.ptype_expr(PrimType::Void)));
                    }

                    Opt::None
                };

                self.label_breaked(id);

                typ = Some(Uty::Expr(self.ptype_expr(PrimType::Never)));

                Expr::Break(id, expr)
            }
            DsExprKind::Continue { label } => {
                let (lab, kind) = if let Some(label) = label {
                    let Some(Label { id, kind, .. }) = self.get_label_by_name(label) else {
                        self.sink.emit(UseOfUndefinedLabel {
                            name: label.clone(),
                            // TODO: add location of the label name
                            loc: expression.loc.clone().unwrap(),
                        });

                        return None;
                    };

                    (*id, kind.clone())
                } else {
                    let Some(&id) = self.label_stack.last() else {
                        self.sink.emit(LabelKwOutsideLoopOrBlock {
                            kw: diags::CONTINUE,
                            loc: expression.loc.clone().unwrap(),
                        });

                        return None;
                    };

                    let kind = self.get_label_by_id(id).kind.clone();

                    (id, kind)
                };

                if !kind.is_loop() {
                    self.sink.emit(CantContinueABlock {
                        loc: expression.loc.clone().unwrap(),
                    });
                }

                typ = Some(Uty::Expr(self.ptype_expr(PrimType::Never)));

                Expr::Continue(lab)
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
                // we don't assign a type it can be anything in the case of a
                // `_ = expr`, it will be checked later
                typ = None;

                Expr::Underscore
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
                let pointee = self.gen_expr(pointee)?;

                if let Some(pointee_t) = self.expr_typ(pointee) {
                    self.push_con(pointee_t, |tyvar| Con::Uty(tyvar, Uty::Expr(type_e)));
                }

                // this type would require evaluation of pointee, and is fairly
                // trivial so we don't assign a type yet.
                typ = None;

                Expr::PtrType(*mutability, pointee)
            }
            DsExprKind::FunPtrType { args: ds_args, ret } => {
                let mut args = Vec::with_capacity(ds_args.len());

                let type_e = self.ptype_expr(PrimType::Type);
                for arg in ds_args {
                    if let Some(arg) = self.gen_expr(arg) {
                        args.push(arg);

                        if let Some(arg_t) = self.expr_typ(arg) {
                            self.push_con(arg_t, |tyvar| Con::Uty(tyvar, Uty::Expr(type_e)));
                        }
                    }
                }

                let ret = self.gen_option_expr(ret.as_deref());

                if let Some(ret) = ret.expand()
                    && let Some(ret_t) = self.expr_typ(ret)
                {
                    self.push_con(ret_t, |tyvar| Con::Uty(tyvar, Uty::Expr(type_e)));
                }

                // this type would require evaluation of the params types and
                // the return type, and is fairly trivial so we don't assign a
                // type yet.
                typ = None;

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

        if let Some(typ) = typ {
            self.body().expr_t.insert(id, typ);
        }

        Some(id)
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
                let typ = self
                    .gen_option_expr(typeexpr)
                    .expand()
                    .map(Uty::Expr)
                    .unwrap_or_else(|| {
                        let tyvar = self.body().type_vars.create_default();

                        Uty::TyVar(tyvar)
                    });

                let val = self.gen_expr(value)?;

                if let Some(val_ty) = self.expr_typ(val) {
                    self.push_con(val_ty, |tyvar| Con::Uty(tyvar, typ));
                }

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
                let e = self.gen_expr(expr)?;

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

        for DsParam {
            name,
            typeexpr,
            loc,
            sym,
        } in params
        {
            let param = params_db.create(Param {
                name: name.clone(),
                typ: Uty::Expr(self.gen_expr(typeexpr)?),
                loc: loc.clone().unwrap(),
            });

            self.map_sym_to_def(sym.unwrap_sym(), DefId::ParamId(param));
        }

        Some(params_db)
    }

    /// Generate the UTIR for a DSIR block.
    fn gen_block(&mut self, block: &DsBlock) -> BlockId {
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

        let tail = self.gen_option_expr(last_expr.as_deref());

        let tail_t = self.expr_typ(tail.expand()).unwrap_or_else(|| {
            let tyvar = self.body().type_vars.create_default();

            Uty::TyVar(tyvar)
        });

        self.body().blocks.create(Block {
            stmts: stmts_set,
            tail,
            typ: tail_t,
            loc: loc.clone().unwrap(),
        })
    }
}
