//! UnTyped Intermediate Representation -- UTIR.

use std::fmt::{self, Display};

use lunc_ast::{Abi, BinOp, Mutability, Spanned, UnOp};
use lunc_entity::{Entity, EntityDb, EntitySet, Opt, SparseMap, entity};
use lunc_seq::sir::PrimType;
use lunc_utils::Span;

/// Orb.
///
/// Contains every item in the orb being build, even the items in sub-modules /
/// extern block.
#[derive(Debug, Clone)]
pub struct Orb {
    pub items: EntityDb<ItemId>,
}

impl Default for Orb {
    fn default() -> Self {
        Orb {
            items: EntityDb::new(),
        }
    }
}

/// Id of an [`Item`].
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct ItemId(u32);

impl Display for ItemId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "i{}", self.index())
    }
}

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

impl Item {
    pub fn body_mut(&mut self) -> &mut Body {
        match self {
            Item::Fundef(Fundef { body, .. })
            | Item::Fundecl(Fundecl { body, .. })
            | Item::GlobalDef(GlobalDef { body, .. })
            | Item::GlobalUninit(GlobalUninit { body, .. }) => body,
            Item::Module(..) => panic!("Item::Module doesn't have a body"),
            Item::ExternBlock(..) => panic!("Item::ExternBlock doesn't have a body"),
        }
    }

    pub fn body(&self) -> &Body {
        match self {
            Item::Fundef(Fundef { body, .. })
            | Item::Fundecl(Fundecl { body, .. })
            | Item::GlobalDef(GlobalDef { body, .. })
            | Item::GlobalUninit(GlobalUninit { body, .. }) => body,
            Item::Module(..) => panic!("Item::Module doesn't have a body"),
            Item::ExternBlock(..) => panic!("Item::ExternBlock doesn't have a body"),
        }
    }
}

/// Fundef -- Function definition.
#[derive(Debug, Clone)]
pub struct Fundef {
    pub name: Spanned<String>,
    pub typ: Opt<ExprId>,
    pub params: EntityDb<ParamId>,
    pub ret_ty: Opt<ExprId>,
    pub entry: BlockId,
    pub body: Body,
    pub loc: Span,
}

impl Default for Fundef {
    /// Create an empty fundef with dummy values.
    fn default() -> Self {
        Fundef {
            name: Spanned {
                node: String::new(),
                loc: Span::ZERO,
            },
            typ: Opt::None,
            params: EntityDb::new(),
            ret_ty: Opt::None,
            entry: BlockId::RESERVED,
            body: Body::default(),
            loc: Span::ZERO,
        }
    }
}

/// Id of a function definition parameter.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct ParamId(u32);

impl Display for ParamId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "p{}", self.index())
    }
}

entity!(ParamId, Param);

/// A parameter
#[derive(Debug, Clone)]
pub struct Param {
    pub name: Spanned<String>,
    pub typ: Uty,
    pub loc: Span,
}

/// Fundecl -- Function declaration.
#[derive(Debug, Clone)]
pub struct Fundecl {
    pub name: Spanned<String>,
    pub typ: Opt<ExprId>,
    pub params: Vec<ExprId>,
    pub ret_ty: Opt<ExprId>,
    pub body: Body,
    pub loc: Span,
}

impl Default for Fundecl {
    fn default() -> Self {
        Fundecl {
            name: Spanned {
                node: String::new(),
                loc: Span::ZERO,
            },
            typ: Opt::None,
            params: Vec::new(),
            ret_ty: Opt::None,
            body: Body::default(),
            loc: Span::ZERO,
        }
    }
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

impl Default for GlobalDef {
    fn default() -> Self {
        GlobalDef {
            name: Spanned {
                node: String::new(),
                loc: Span::ZERO,
            },
            mutability: Mutability::Not,
            typ: Opt::None,
            value: ExprId::RESERVED,
            body: Body::default(),
            loc: Span::ZERO,
        }
    }
}

/// GlobalUninit -- Global definition.
#[derive(Debug, Clone)]
pub struct GlobalUninit {
    pub name: Spanned<String>,
    pub typ: ExprId,
    pub body: Body,
    pub loc: Span,
}

impl Default for GlobalUninit {
    fn default() -> Self {
        GlobalUninit {
            name: Spanned {
                node: String::new(),
                loc: Span::ZERO,
            },
            typ: ExprId::RESERVED,
            body: Body::default(),
            loc: Span::ZERO,
        }
    }
}

/// Module.
#[derive(Debug, Clone)]
pub struct Module {
    pub name: String,
    pub items: EntitySet<ItemId>,
    pub loc: Span,
}

impl Default for Module {
    fn default() -> Self {
        Module {
            name: String::new(),
            items: EntitySet::new(),
            loc: Span::ZERO,
        }
    }
}

/// ExternBlock -- Extern block.
#[derive(Debug, Clone)]
pub struct ExternBlock {
    pub abi: Abi,
    pub items: EntitySet<ItemId>,
    pub loc: Span,
}

impl Default for ExternBlock {
    fn default() -> Self {
        ExternBlock {
            abi: Abi::default(),
            items: EntitySet::new(),
            loc: Span::ZERO,
        }
    }
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
    /// Character, see [`DsExprKind::Lit`].
    ///
    /// [`DsExprKind::Lit`]: lunc_desugar::DsExprKind::Lit
    Char(char),
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
    Param(ParamId),
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
    Loop(LabelId, BlockId),
    /// Return expression, returns the function with value `.0`, see
    /// [`DsExprKind::Return`].
    ///
    /// [`DsExprKind::Return`]: lunc_desugar::DsExprKind::Return
    Return(Opt<ExprId>),
    /// Break expression, with label `.0` and value `.1`, see
    /// [`DsExprKind::Break`].
    ///
    /// [`DsExprKind::Break`]: lunc_desugar::DsExprKind::Break
    Break(LabelId, Opt<ExprId>),
    /// Continue expression, with label `.0`, see [`DsExprKind::Continue`].
    ///
    /// [`DsExprKind::Continue`]: lunc_desugar::DsExprKind::Continue
    Continue(LabelId),
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
    /// Primitive type, it's a [`DsExprKind::Path`] in Dsir.
    ///
    /// [`DsExprKind::Path`]: lunc_desugar::DsExprKind::Path
    PrimType(PrimType),
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

impl Display for ExtExpr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if let Some(item) = self.0.expand() {
            write!(f, "ext({item}, {})", self.1)
        } else {
            Display::fmt(&self.1, f)
        }
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
    BindingDef(BindingId),
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
    pub stmts: EntitySet<StmtId>,
    pub tail: Opt<ExprId>,
    pub typ: Uty,
    pub loc: Span,
}

/// Local reference to a user binding see [`Stmt::BindingDef`].
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct BindingId(u32);

impl Display for BindingId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "bind{}", self.index())
    }
}

entity!(BindingId, BindingDef);

/// Binding def.
#[derive(Debug, Clone)]
pub struct BindingDef {
    pub name: Spanned<String>,
    pub mutability: Mutability,
    pub typ: Uty,
    pub val: ExprId,
}

/// Local reference to a label.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct LabelId(u32);

impl Display for LabelId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "l{}", self.index())
    }
}

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

impl LabelKind {
    pub fn can_have_val(&self) -> bool {
        matches!(self, LabelKind::InfiniteLoop | LabelKind::Block)
    }

    pub fn is_loop(&self) -> bool {
        matches!(self, LabelKind::InfiniteLoop | LabelKind::PredicateLoop)
    }
}

impl Display for LabelKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Block => write!(f, "block"),
            Self::InfiniteLoop => write!(f, "loop"),
            Self::PredicateLoop => write!(f, "while"),
        }
    }
}

/// A label.
#[derive(Debug, Clone)]
pub struct Label {
    pub id: LabelId,
    pub name: Option<Spanned<String>>,
    pub typ: Option<Uty>,
    pub kind: LabelKind,
    /// Did we `break` out of this label?
    pub break_out: bool,
}

/// Something that can hold, [`Expr`], [`Stmt`], [`Block`] and more.
#[derive(Debug, Clone)]
pub struct Body {
    pub labels: EntityDb<LabelId>,
    pub bindings: EntityDb<BindingId>,
    pub stmts: EntityDb<StmtId>,
    pub exprs: EntityDb<ExprId>,
    pub blocks: EntityDb<BlockId>,

    /// Expression type with constraints if any, in a "Hindley–Milner" Type
    /// System fashion.
    pub expr_t: SparseMap<ExprId, Uty>,
    /// Type-variables in the HM type system
    pub type_vars: EntityDb<TyVar>,
    /// Constraints on the type-variables.
    pub constraints: Constraints,

    pub expr_locs: SparseMap<ExprId, Span>,
    pub stmt_locs: SparseMap<StmtId, Span>,
}

impl Default for Body {
    fn default() -> Self {
        Body {
            labels: EntityDb::new(),
            bindings: EntityDb::new(),
            stmts: EntityDb::new(),
            exprs: EntityDb::new(),
            blocks: EntityDb::new(),

            expr_t: SparseMap::new(),
            type_vars: EntityDb::new(),
            constraints: Constraints(Vec::new()),

            expr_locs: SparseMap::new(),
            stmt_locs: SparseMap::new(),
        }
    }
}

/// A type-variable.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct TyVar(u32);

entity!(TyVar, ());

impl Display for TyVar {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "'T{}", self.index())
    }
}

/// UTIR-type, either a reference to an expression or a typevar
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Uty {
    Expr(ExprId),
    TyVar(TyVar),
}

impl Display for Uty {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Expr(expr) => write!(f, "{expr}"),
            Self::TyVar(tyvar) => write!(f, "{tyvar}"),
        }
    }
}

impl From<ExprId> for Uty {
    fn from(value: ExprId) -> Self {
        Uty::Expr(value)
    }
}

impl From<TyVar> for Uty {
    fn from(value: TyVar) -> Self {
        Uty::TyVar(value)
    }
}

/// A list of constraints
#[derive(Debug, Clone, Default)]
pub struct Constraints(pub Vec<Con>);

/// Type constraint
#[derive(Debug, Clone)]
pub enum Con {
    /// The type-var represents an integer-like expression (used for integer
    /// literals without types).
    ///
    /// `tyvar = integer`
    Integer(TyVar),
    /// Same as `Con::Integer` but for float-literals
    ///
    /// `tyvar = float`
    Float(TyVar),
    /// The type-variable must be of type `.1`
    ///
    /// `tyvar = uty`
    Uty(TyVar, Uty),
}

/// Any id of the UTIR that represents a definition, primarily used to convert
/// DSIR symbols to the correct id.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum DefId {
    ParamId(ParamId),
    BindingId(BindingId),
    ItemId(ItemId),
}
