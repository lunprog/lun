//! UnTyped Intermediate Representation -- UTIR.

use std::fmt::{self, Display};

use lunc_ast::{Abi, BinOp, Mutability, Spanned, UnOp};
use lunc_entity::{Entity, EntityDb, Opt, SparseMap, entity};
use lunc_utils::Span;

/// Orb.
///
/// Contains every item in the orb being build, even the items in sub-modules /
/// extern block.
#[derive(Debug, Clone)]
pub struct Orb {
    pub items: EntityDb<ItemId>,
}

/// Id of an [`Item`].
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct ItemId(u32);

entity!(ItemId, Item);

/// Item.
#[derive(Debug, Clone)]
pub enum Item {
    Fundef(Fundef),
    Fundecl(Fundecl),
    GlobalDef(GlobalDef),
    GlobalUninit(GlobalUninit),
    Module(Module),
    ExternBlock(ExternBlock),
}

/// Fundef -- Function definition.
#[derive(Debug, Clone)]
pub struct Fundef {
    pub name: Spanned<String>,
    pub typ: Opt<ExprId>,
    pub params: Vec<Spanned<ExprId>>,
    pub ret_ty: Opt<ExprId>,
    pub body: Body,
    pub entry: BlockId,
    pub loc: Span,
}

/// Fundecl -- Function declaration.
#[derive(Debug, Clone)]
pub struct Fundecl {
    pub name: Spanned<String>,
    pub typ: Opt<ExprId>,
    pub params: Vec<Spanned<ExprId>>,
    pub ret_ty: Opt<ExprId>,
    pub body: Body,
    pub loc: Span,
}

/// GlobalDef -- Global definition.
#[derive(Debug, Clone)]
pub struct GlobalDef {
    pub name: Spanned<String>,
    pub mutability: Mutability,
    pub typ: Opt<ExprId>,
    pub value: ExprId,
    pub body: Body,
    pub loc: Span,
}

/// GlobalUninit -- Global definition.
#[derive(Debug, Clone)]
pub struct GlobalUninit {
    pub name: Spanned<String>,
    pub typ: ExprId,
    pub body: Body,
    pub loc: Span,
}

/// Module.
#[derive(Debug, Clone)]
pub struct Module {
    pub name: String,
    pub items: Vec<ItemId>,
    pub loc: Span,
}

/// ExternBlock -- Extern block.
#[derive(Debug, Clone)]
pub struct ExternBlock {
    pub abi: Abi,
    pub items: Vec<ItemId>,
    pub loc: Span,
}

/// Local reference to an [`Expr`] in something that can store it.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct ExprId(u32);

impl Display for ExprId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "e{}", self.index())
    }
}

entity!(ExprId, Expr);

/// An expression.
///
/// By default an expression is *untyped* unless an expression is `typed(type,
/// val)`, which tells the later stages that `val` must be able to be a `typ`.
/// Note that it doesn't perform type conversion by default.
#[derive(Debug, Clone)]
pub enum Expr {
    /// Integer, see [`DsExprKind::Lit`].
    ///
    /// [`DsExprKind::Lit`]: lunc_desugar::DsExprKind::Lit
    Int(u128),
    /// Integer, see [`DsExprKind::Lit`].
    ///
    /// [`DsExprKind::Lit`]: lunc_desugar::DsExprKind::Lit
    Float(f64),
    /// Integer, see [`DsExprKind::Lit`].
    ///
    /// [`DsExprKind::Lit`]: lunc_desugar::DsExprKind::Lit
    Str(Box<str>),
    /// Integer, see [`DsExprKind::Lit`].
    ///
    /// [`DsExprKind::Lit`]: lunc_desugar::DsExprKind::Lit
    CStr(Box<str>),
    /// Bool, see [`DsExprKind::BoolLit`].
    ///
    /// [`DsExprKind::BoolLit`]: lunc_desugar::DsExprKind::BoolLit
    Bool(bool),
    /// Reference to an Item, see [`DsExprKind::Path`].
    ///
    /// [`DsExprKind::Path`]: lunc_desugar::DsExprKind::Path
    Item(ItemId),
    /// Reference to a function parameter, see [`DsExprKind::Path`].
    ///
    /// [`DsExprKind::Path`]: lunc_desugar::DsExprKind::Path
    Param(u32),
    /// Reference to a user-binding, see [`DsExprKind::Path`].
    ///
    /// [`DsExprKind::Path`]: lunc_desugar::DsExprKind::Path
    Binding(BindingId),
    /// Binary operation between lhs (`.0`) and rhs (`.2`), see
    /// [`DsExprKind::Binary`].
    ///
    /// [`DsExprKind::Binary`]: lunc_desugar::DsExprKind::Binary
    Binary(ExprId, BinOp, ExprId),
    /// Unary operation on expr (`.1`), see [`DsExprKind::Unary`].
    ///
    /// [`DsExprKind::Unary`]: lunc_desugar::DsExprKind::Unary
    Unary(UnOp, ExprId),
    /// Borrow of expr (`.1`), maybe mutable, see [`DsExprKind::Borrow`].
    ///
    /// [`DsExprKind::Borrow`]: lunc_desugar::DsExprKind::Borrow
    Borrow(Mutability, ExprId),
    /// Call the `callee`, with `args` as arguments, see [`DsExprKind::Call`].
    ///
    /// [`DsExprKind::Call`]: lunc_desugar::DsExprKind::Call
    Call { callee: ExprId, args: Vec<ExprId> },
    /// If-else expression, see [`DsExprKind::If`].
    ///
    /// [`DsExprKind::If`]: lunc_desugar::DsExprKind::If
    If {
        cond: ExprId,
        then_e: ExprId,
        else_e: Opt<ExprId>,
    },
    /// Block (`.1`) that may be labeled (`.0`), see [`DsExprKind::Block`].
    ///
    /// [`DsExprKind::Block`]: lunc_desugar::DsExprKind::Block
    Block(Opt<LabelId>, BlockId),
    /// `loop`-expression with label (`.0`) and body (`.1`), see [`DsExprKind::Loop`].
    ///
    /// [`DsExprKind::Loop`]: lunc_desugar::DsExprKind::Loop
    Loop(Opt<LabelId>, BlockId),
    /// Return expression, returns the function with value `.0`, see
    /// [`DsExprKind::Return`].
    ///
    /// [`DsExprKind::Return`]: lunc_desugar::DsExprKind::Return
    Return(Opt<ExprId>),
    /// Break expression, with label `.0` and value `.1`, see
    /// [`DsExprKind::Break`].
    ///
    /// [`DsExprKind::Break`]: lunc_desugar::DsExprKind::Break
    Break(Opt<LabelId>, Opt<ExprId>),
    /// Continue expression, with label `.0`, see [`DsExprKind::Continue`].
    ///
    /// [`DsExprKind::Continue`]: lunc_desugar::DsExprKind::Continue
    Continue(Opt<LabelId>),
    /// Underscore, used to discard the result of an expression in an assignment
    /// see [`DsExprKind::Underscore`].
    ///
    /// [`DsExprKind::Underscore`]: lunc_desugar::DsExprKind::Underscore
    Underscore,
    /// Pointer type, see [`DsExprKind::PointerType`].
    ///
    /// [`DsExprKind::PointerType`]: lunc_desugar::DsExprKind::PointerType
    PtrType(Mutability, ExprId),
    /// Function pointer, with params types `.0` and return type `.1`, see [`DsExprKind::FunPtrType`].
    ///
    /// [`DsExprKind::FunPtrType`]: lunc_desugar::DsExprKind::FunPtrType
    FunptrType(Vec<ExprId>, Opt<ExprId>),

    //
    // UTIR SPECIFIC
    //
    /// Make the expr `val` have the type `typ`.
    Typed { typ: ExtExpr, val: ExprId },
    /// The return type of the function
    RetTy,
}

/// External reference to an expr ([ExprId]) in the local item or in the
/// [ItemId] if any.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct ExtExpr(Opt<ItemId>, ExprId);

impl ExtExpr {
    /// New external expression (`expr`) in the `item`.
    pub fn ext(item: ItemId, expr: ExprId) -> ExtExpr {
        ExtExpr(Opt::Some(item), expr)
    }

    /// New local expression (`expr`).
    pub const fn local(expr: ExprId) -> ExtExpr {
        ExtExpr(Opt::None, expr)
    }
}

/// Local reference to an [`Stmt`] in something that can store it.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct StmtId(u32);

impl Display for StmtId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "s{}", self.index())
    }
}

entity!(StmtId, Stmt);

/// Statement.
#[derive(Debug, Clone)]
pub enum Stmt {
    /// User binding, see [`DsStmtKind::BindingDef`].
    ///
    /// [`DsStmtKind::BindingDef`]: lunc_desugar::DsStmtKind::BindingDef
    BindingDef { id: BindingId },
    /// Expression, see [`DsStmtKind::BindingDef`].
    ///
    /// [`DsStmtKind::BindingDef`]: lunc_desugar::DsStmtKind::BindingDef
    Expression(ExprId),
}

/// Local reference to a block.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct BlockId(u32);

impl Display for BlockId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "b{}", self.index())
    }
}

entity!(BlockId, Block);

/// A block.
#[derive(Debug, Clone)]
pub struct Block {
    pub stmts: Vec<StmtId>,
    pub tail: Opt<ExprId>,
    pub loc: Span,
}

/// Local reference to a user binding see [`Stmt::BindingDef`].
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct BindingId(u32);

entity!(BindingId, BindingDef);

/// Binding def.
#[derive(Debug, Clone)]
pub struct BindingDef {
    pub mutability: Mutability,
    pub typ: Opt<ExprId>,
    pub val: ExprId,
}

/// Local reference to a label.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct LabelId(u32);

entity!(LabelId, Label);

/// Kind of label
#[derive(Debug, Clone)]
pub enum LabelKind {
    /// the label is on a block, like
    ///
    /// ```lun
    /// blk: {};
    /// ```
    Block,
    /// the label is on a infinite loop, like
    ///
    /// ```lun
    /// lab: loop {};
    /// ```
    InfiniteLoop,
    /// the label is on a predicate loop, like
    ///
    /// ```lun
    /// lab: while {};
    /// ```
    PredicateLoop,
}

/// A label.
#[derive(Debug, Clone)]
pub struct Label {
    pub id: LabelId,
    pub name: Option<Spanned<String>>,
    pub typ: ExprId,
    pub kind: LabelKind,
}

/// Something that can hold, [`Expr`], [`Stmt`], [`Block`] and more.
#[derive(Debug, Clone)]
pub struct Body {
    pub stmts: EntityDb<StmtId>,
    pub exprs: EntityDb<ExprId>,
    pub blocks: EntityDb<BlockId>,
    pub labels: EntityDb<LabelId>,
    pub bindings: EntityDb<BindingId>,

    pub expr_locs: SparseMap<ExprId, Span>,
    pub stmt_locs: SparseMap<StmtId, Span>,
}
