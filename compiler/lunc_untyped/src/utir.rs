//! UnTyped Intermediate Representation -- UTIR.

use std::{
    fmt::{self, Debug, Display},
    io::{self, Write},
};

use lunc_ast::{Abi, BinOp, Mutability, Path, Spanned, UnOp};
use lunc_entity::{Entity, EntityDb, EntitySet, Opt, SparseMap, entity};
use lunc_seq::sir::PrimType;
use lunc_utils::{
    Span, opt_unreachable,
    pretty::{PrettyCtxt, PrettyDump},
};

use crate::diags::PreMt;

/// Orb.
///
/// Contains every item in the orb being build, even the items in sub-modules /
/// extern block.
#[derive(Debug, Clone, Hash)]
pub struct Orb {
    pub items: EntityDb<ItemId>,
    pub flavor: Flavor,
}

impl Default for Orb {
    fn default() -> Self {
        Orb {
            items: EntityDb::new(),
            flavor: Flavor::Generated,
        }
    }
}

/// Flavor of UTIR.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Flavor {
    /// The "generated UTIR" dialect, everything is possible.
    ///
    /// # Note
    ///
    /// [`Expr::ExtType`] -- is never generated.
    Generated,
    /// The dialect used by the unifier to unify the type-variables.
    ///
    /// The following variants are not allowed:
    /// * [`Expr::TypeofItem`]
    Unified,
}

impl Flavor {
    /// Get the next flavor of utir after `self`.
    pub fn next(&self) -> Flavor {
        match self {
            Flavor::Generated => Flavor::Unified,
            Flavor::Unified => panic!("no following flavor after `Flavor::Unified`"),
        }
    }

    /// Set the flavor to the next one.
    pub fn set_next(&mut self) {
        *self = self.next()
    }

    /// String slice representing the flavor.
    pub fn as_str(&self) -> &'static str {
        match self {
            Flavor::Generated => "generated",
            Flavor::Unified => "unified",
        }
    }
}

impl<E> PrettyDump<E> for Flavor {
    fn try_dump(&self, ctx: &mut PrettyCtxt, _: &E) -> io::Result<()> {
        write!(ctx.out, "{}", self.as_str())
    }
}

/// Id of an [`Item`].
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct ItemId(u32);

impl Display for ItemId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "i{}", self.index())
    }
}

impl Debug for ItemId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        <ItemId as Display>::fmt(self, f)
    }
}

entity!(ItemId, Item);

/// Item.
#[derive(Debug, Clone, Hash)]
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

    pub fn path(&self) -> &Path {
        match self {
            Item::Fundef(Fundef { path, .. })
            | Item::Fundecl(Fundecl { path, .. })
            | Item::GlobalDef(GlobalDef { path, .. })
            | Item::GlobalUninit(GlobalUninit { path, .. }) => path,
            Item::Module(..) => panic!("Item::Module doesn't have a path"),
            Item::ExternBlock(..) => panic!("Item::ExternBlock doesn't have a path"),
        }
    }

    pub fn typ(&self) -> Uty {
        match self {
            Item::Fundef(Fundef { typ, .. })
            | Item::Fundecl(Fundecl { typ, .. })
            | Item::GlobalUninit(GlobalUninit { typ, .. }) => Uty::Expr(*typ),
            Item::GlobalDef(GlobalDef { typ, .. }) => *typ,
            Item::Module(..) => panic!("Item::Module doesn't have a type"),
            Item::ExternBlock(..) => panic!("Item::ExternBlock doesn't have a type"),
        }
    }
    pub fn loc(&self) -> &Span {
        match self {
            Item::Fundef(Fundef { loc, .. })
            | Item::Fundecl(Fundecl { loc, .. })
            | Item::GlobalDef(GlobalDef { loc, .. })
            | Item::GlobalUninit(GlobalUninit { loc, .. })
            | Item::Module(Module { loc, .. })
            | Item::ExternBlock(ExternBlock { loc, .. }) => loc,
        }
    }
}

/// Fundef -- Function definition.
#[derive(Debug, Clone, Hash)]
pub struct Fundef {
    pub name: Spanned<String>,
    pub path: Path,
    pub typ: ExprId,
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
            path: Path::new(),
            typ: ExprId::RESERVED,
            params: EntityDb::new(),
            ret_ty: Opt::None,
            entry: BlockId::RESERVED,
            body: Body::default(),
            loc: Span::ZERO,
        }
    }
}

/// Id of a function definition parameter.
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct ParamId(u32);

impl Display for ParamId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "p{}", self.index())
    }
}

impl Debug for ParamId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        Display::fmt(self, f)
    }
}

entity!(ParamId, Param);

/// A parameter
#[derive(Debug, Clone, Hash)]
pub struct Param {
    pub name: Spanned<String>,
    pub typ: Uty,
    pub loc: Span,
}

/// Fundecl -- Function declaration.
#[derive(Debug, Clone, Hash)]
pub struct Fundecl {
    pub name: Spanned<String>,
    pub path: Path,
    pub typ: ExprId,
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
            path: Path::new(),
            typ: ExprId::RESERVED,
            params: Vec::new(),
            ret_ty: Opt::None,
            body: Body::default(),
            loc: Span::ZERO,
        }
    }
}

/// GlobalDef -- Global definition.
#[derive(Debug, Clone, Hash)]
pub struct GlobalDef {
    pub name: Spanned<String>,
    pub path: Path,
    pub mutability: Mutability,
    pub typ: Uty,
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
            path: Path::new(),
            mutability: Mutability::Not,
            typ: Uty::Expr(ExprId::RESERVED),
            value: ExprId::RESERVED,
            body: Body::default(),
            loc: Span::ZERO,
        }
    }
}

/// GlobalUninit -- Global definition.
#[derive(Debug, Clone, Hash)]
pub struct GlobalUninit {
    pub name: Spanned<String>,
    pub path: Path,
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
            path: Path::new(),
            typ: ExprId::RESERVED,
            body: Body::default(),
            loc: Span::ZERO,
        }
    }
}

/// Module.
#[derive(Debug, Clone, Hash)]
pub struct Module {
    pub name: String,
    pub path: Path,
    pub items: EntitySet<ItemId>,
    pub loc: Span,
}

impl Default for Module {
    fn default() -> Self {
        Module {
            name: String::new(),
            path: Path::new(),
            items: EntitySet::new(),
            loc: Span::ZERO,
        }
    }
}

/// ExternBlock -- Extern block.
#[derive(Debug, Clone, Hash)]
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
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct ExprId(u32);

impl Display for ExprId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "e{}", self.index())
    }
}

impl Debug for ExprId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        Display::fmt(self, f)
    }
}

entity!(ExprId, Expr);

/// IEEE-754 floating point number
#[repr(transparent)]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Ieee754(u64);

impl Ieee754 {
    /// Converts a f64 to a Ieee754
    pub fn from_f64(f: f64) -> Ieee754 {
        Ieee754(f.to_bits())
    }

    pub fn into_f64(self) -> f64 {
        f64::from_bits(self.0)
    }
}

impl Display for Ieee754 {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.into_f64())
    }
}

/// An expression.
#[derive(Debug, Clone, Hash, PartialEq)]
pub enum Expr {
    /// Integer, see [`DsExprKind::Lit`].
    ///
    /// [`DsExprKind::Lit`]: lunc_desugar::DsExprKind::Lit
    Int(u128),
    /// Character, see [`DsExprKind::Lit`].
    ///
    /// [`DsExprKind::Lit`]: lunc_desugar::DsExprKind::Lit
    Char(char),
    /// Float, see [`DsExprKind::Lit`].
    ///
    /// [`DsExprKind::Lit`]: lunc_desugar::DsExprKind::Lit
    Float(Ieee754),
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
    /// Anonymous function definition/declaration type, it's a unique type per
    /// item, it doesn't have a textual representation in the lun syntax, it's
    /// here so that we can assign a type to functions when they don't have
    /// a type.
    ///
    /// e.g:
    /// ```lun
    /// foo :: fun(a: u8, b: u8) -> u8 {
    ///     a + b
    /// }
    /// // this function would have type `fun(u8, u8) -> u8 { example::foo }`
    /// ```
    FundefType {
        fundef: ItemId,
        params: Vec<ExprId>,
        ret: ExprId,
    },
    /// Type of the specified item, should not be used if the item id is the
    /// same of the item containing the expression.
    TypeofItem(ItemId),
    /// An expression in a foreign item.
    ///
    /// # Note
    ///
    /// This type doesn't represent an expression in Lun, it's an internal thing.
    ExtExpr(Ext<ExprId>),
    /// A type in a foreign item.
    ///
    /// # Note
    ///
    /// This type doesn't represent an expression in Lun, it's an internal thing.
    ExtType(Ext<Uty>),
}

impl Expr {
    /// Returns the return type expression if it is a fundef-type or funptr-type
    /// expression.
    pub fn fun_ret(&self) -> Option<ExprId> {
        match self {
            Expr::FunptrType(_, ret) => ret.expand(),
            Expr::FundefType { ret, .. } => Some(*ret),
            _ => None,
        }
    }
}

/// External reference to an entity in the [ItemId].
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Ext<E> {
    pub item: ItemId,
    pub ent: E,
}

impl<E: Display> Display for Ext<E> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}@{}", self.ent, self.item)
    }
}

/// Local reference to an [`Stmt`] in something that can store it.
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct StmtId(u32);

impl Display for StmtId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "s{}", self.index())
    }
}

impl Debug for StmtId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        Display::fmt(self, f)
    }
}

entity!(StmtId, Stmt);

/// Statement.
#[derive(Debug, Clone, Hash)]
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
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct BlockId(u32);

impl Display for BlockId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "b{}", self.index())
    }
}

impl Debug for BlockId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        Display::fmt(self, f)
    }
}

entity!(BlockId, Block);

/// A block.
#[derive(Debug, Clone, Hash)]
pub struct Block {
    pub stmts: EntitySet<StmtId>,
    pub tail: Opt<ExprId>,
    pub typ: Uty,
    pub loc: Span,
}

/// Local reference to a user binding see [`Stmt::BindingDef`].
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct BindingId(u32);

impl Display for BindingId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "bind{}", self.index())
    }
}

impl Debug for BindingId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        Display::fmt(self, f)
    }
}

entity!(BindingId, BindingDef);

/// Binding def.
#[derive(Debug, Clone, Hash)]
pub struct BindingDef {
    pub name: Spanned<String>,
    pub mutability: Mutability,
    pub typ: Uty,
    pub val: ExprId,
}

/// Local reference to a label.
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct LabelId(u32);

impl Display for LabelId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "l{}", self.index())
    }
}

impl Debug for LabelId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        Display::fmt(self, f)
    }
}

entity!(LabelId, Label);

/// Kind of label
#[derive(Debug, Clone, Hash)]
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
#[derive(Debug, Clone, Hash)]
pub struct Label {
    pub id: LabelId,
    pub name: Option<Spanned<String>>,
    pub tyvar: TyVar,
    /// Location of the first constraint on the type of the label.
    pub tyvar_loc: Option<Span>,
    pub kind: LabelKind,
    /// Did we `break` out of this label?
    pub break_out: bool,
}

/// Something that can hold, [`Expr`], [`Stmt`], [`Block`] and more.
#[derive(Debug, Clone, Hash)]
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
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct TyVar(u32);

entity!(TyVar, ());

impl Display for TyVar {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "'T{}", self.index())
    }
}

impl Debug for TyVar {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        Display::fmt(self, f)
    }
}

/// UTIR-type, either a reference to an expression or a typevar
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub enum Uty {
    Expr(ExprId),
    TyVar(TyVar),
    /// Integer-able type
    Integer,
    /// Float-able type
    Float,
}

impl Uty {
    /// A weak-uty is Integer or Float.
    ///
    /// They are "weak" because in the substitution they can be replaced.
    pub fn is_weak(&self) -> bool {
        matches!(self, Uty::Integer | Uty::Float)
    }

    /// Opposite of `is_weak`.
    #[inline]
    pub fn is_strong(&self) -> bool {
        !self.is_weak()
    }
}

impl Display for Uty {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Expr(expr) => write!(f, "{expr}"),
            Self::TyVar(tyvar) => write!(f, "{tyvar}"),
            Self::Integer => write!(f, "{{integer}}"),
            Self::Float => write!(f, "{{float}}"),
        }
    }
}

impl Debug for Uty {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        Display::fmt(self, f)
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
#[derive(Debug, Clone, Default, Hash)]
pub struct Constraints(pub Vec<Con>);

/// Type constraint
///
/// `uty = uty`
///
/// # Direction of this constraint.
///
/// You want to have the right uty to be the expected type and the left one
/// the "found" one, like that: `found = expected`.
#[derive(Debug, Clone, Hash)]
pub struct Con {
    pub lhs: Uty,
    pub rhs: Uty,
    pub pre: PreMt,
}

/// Any id of the UTIR that represents a definition, primarily used to convert
/// DSIR symbols to the correct id.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum DefId {
    ParamId(ParamId),
    BindingId(BindingId),
    ItemId(ItemId),
}

/// UTIR type, it is very much similar with [SIR types](lunc_seq::sir::Type),
/// because it represents the same thing but at different stages.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Type {
    /// Primitive type
    PrimType(PrimType),
    /// A pointer
    Ptr(Mutability, Box<Type>),
    /// A function pointer
    FunPtr(Vec<Type>, Box<Type>),
    /// Anonymous type of a function definition/declaration. Each function has a unique type.
    ///
    /// e.g:
    /// ```lun
    /// foo :: fun(a: u8, b: u8) -> u8 {
    ///     a + b
    /// }
    /// // this function would have type `fun(u8, u8) -> u8 { example::foo }`
    /// ```
    FunDef {
        fundef: ItemId,
        params: Vec<Type>,
        ret: Box<Type>,
    },
    /// A reference to an item with "type" `Type`.
    Item(ItemId),
}

impl Type {
    /// Returns true if a type has the specified ability, false otherwise.
    pub fn has_ability(&self, ability: TypeAbility) -> bool {
        match self {
            Type::PrimType(ptype) if ptype.is_integer() && ability == TypeAbility::Integer => true,
            Type::PrimType(ptype) if ptype.is_float() && ability == TypeAbility::Float => true,
            _ => false,
        }
    }
}

/// Ability of a type to store some sort of data
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TypeAbility {
    /// A type able to store integer like values
    Integer,
    /// A type able to store float like values
    Float,
}

impl TypeAbility {
    /// # Safety
    ///
    /// Calling this function with a `Uty` different than
    /// Uty::Float/Uty::Integer can cause UB.
    pub fn from_uty(uty: Uty) -> TypeAbility {
        match uty {
            Uty::Integer => TypeAbility::Integer,
            Uty::Float => TypeAbility::Float,
            _ => {
                // SAFETY: the caller guarantees it is never reached
                opt_unreachable!()
            }
        }
    }
}

impl Display for TypeAbility {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Integer => write!(f, "{{integer}}"),
            Self::Float => write!(f, "{{float}}"),
        }
    }
}
