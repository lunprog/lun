//! Sequential Intermediate Representation of Lun.

use std::fmt::{self, Display};

use lunc_ast::{Abi, Comptime, Mutability, Path};
use lunc_desugar::DsParam;
use lunc_entity::{Entity, EntityDb, SparseMap, entity};
use lunc_utils::Span;

use crate::builder::{CtBuilder, RtBuilder};

/// A Lun orb.
#[derive(Debug, Clone)]
pub struct Orb {
    pub items: EntityDb<ItemId>,
}

impl Orb {
    /// Create a new empty orb.
    pub fn new() -> Orb {
        Orb {
            items: EntityDb::new(),
        }
    }
}

impl Default for Orb {
    fn default() -> Self {
        Orb::new()
    }
}

/// Id of an [`Item`].
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct ItemId(u32);

entity!(ItemId, Item);

/// An item.
#[derive(Debug, Clone)]
pub enum Item {
    Fundef(Fundef),
    Fundecl(Fundecl),
    GlobalUninit(GlobalUninit),
    GlobalDef(GlobalDef),
}

impl Item {
    /// Returns the path of the item.
    pub fn path(&self) -> &Path {
        match self {
            Self::Fundef(fundef) => &fundef.path,
            Self::Fundecl(fundecl) => &fundecl.path,
            Self::GlobalUninit(glob_uninit) => &glob_uninit.path,
            Self::GlobalDef(globdef) => &globdef.path,
        }
    }
}

/// Usually, a SIR-body ([CtBody] or [CrtBody]) capable of storing [`Local`]s
/// and their [debug information].
///
/// [debug information]: crate::sir::LocalDbg
pub trait LocalAble: fmt::Debug {
    // LOCALS

    /// Get the locals database.
    fn locals(&self) -> &EntityDb<LocalId>;

    /// Mutable [`LocalAble::locals`].
    fn locals_mut(&mut self) -> &mut EntityDb<LocalId>;

    /// Get the `local`.
    fn get_local(&self, local: LocalId) -> &Local {
        self.locals().get(local)
    }

    /// Mutable [`LocalAble::get_local`]
    fn get_local_mut(&mut self, local: LocalId) -> &mut Local {
        self.locals_mut().get_mut(local)
    }

    /// Create a new local
    fn new_local(&mut self, comptime: Comptime, mutability: Mutability, typ: Type) -> LocalId {
        self.locals_mut().create_with(|id| Local {
            comptime,
            id,
            mutability,
            typ,
        })
    }

    /// Create a new local and associate it debug information
    fn new_local_with_dbg(
        &mut self,
        comptime: Comptime,
        mutability: Mutability,
        kind: LocalKind,
        name: String,
        typ: Type,
        loc: Span,
    ) -> LocalId {
        let local = self.new_local(comptime, mutability, typ);

        self.local_dbgs_mut().insert(
            local,
            LocalDbg {
                id: local,
                name,
                kind,
                loc,
            },
        );

        local
    }

    // LOCAL DBG INFOS

    /// Get the local debug infos map.
    fn local_dbgs(&self) -> &SparseMap<LocalId, LocalDbg>;

    /// Mutable [`LocalAble::local_dbgs`]
    fn local_dbgs_mut(&mut self) -> &mut SparseMap<LocalId, LocalDbg>;

    /// Get the debug information of `local` if any.
    fn get_local_dbg(&self, local: LocalId) -> Option<&LocalDbg> {
        self.local_dbgs().get(local)
    }
}

/// A SIR body capable of **c**ompile-**t**ime.
pub trait CtBody: LocalAble {
    // COMPTIME BASIC-BLOCKS

    /// Get the compile-time basic-blocks
    fn ct_blocks(&self) -> &EntityDb<Bb>;

    /// Mutable [`CtBody::ct_blocks`].
    fn ct_blocks_mut(&mut self) -> &mut EntityDb<Bb>;

    /// Create a compile-time basic block without a terminator.
    fn new_ctbb(&mut self) -> Bb {
        self.ct_blocks_mut().create_with(|id| BasicBlock {
            id,
            comptime: Comptime::Yes,
            stmts: Vec::new(),
            term: None,
        })
    }
}

/// A **c**ompile time and **r**un**t**ime capable body.
pub trait CrtBody: CtBody + LocalAble {
    /// Get the non-comptime basic-blocks.
    fn blocks(&self) -> &EntityDb<Bb>;

    /// Mutable [`CrtBody::blocks`].
    fn blocks_mut(&mut self) -> &mut EntityDb<Bb>;

    /// Create a new empty basic-block without a terminator.
    fn new_bb(&mut self) -> Bb {
        self.blocks_mut().create_with(|id| BasicBlock {
            id,
            comptime: Comptime::No,
            stmts: Vec::new(),
            term: None,
        })
    }
}

/// SIR body, contains the temporaries, user-bindings and basic blocks of a
/// function definition or a global definition
#[derive(Debug, Clone)]
pub struct Body {
    /// Locals
    pub locals: EntityDb<LocalId>,
    /// Local debug information
    pub local_dbgs: SparseMap<LocalId, LocalDbg>,
    /// Compile-time only basic blocks
    pub comptime_bbs: EntityDb<Bb>,
    /// Basic-blocks.
    pub bbs: EntityDb<Bb>,
}

impl Body {
    /// Create a [`SirBuilder`] for the basic-blocks.
    ///
    /// See `Body::ct_builder` for the compile-time version.
    ///
    /// [`SirBuilder`]: crate::builder::SirBuilder
    pub fn builder<'body>(&'body mut self) -> RtBuilder<'body> {
        // RtBuilder { body: self }
        todo!()
    }

    /// Create a [`SirBuilder`] for the compile-time basic-blocks.
    ///
    /// See `Body::builder` for the *non* compile-time version.
    ///
    /// [`SirBuilder`]: crate::builder::SirBuilder
    pub fn ct_builder<'body>(&'body mut self) -> CtBuilder<'body> {
        // CtBuilder { body: self }
        todo!()
    }
}

impl LocalAble for Body {
    fn locals(&self) -> &EntityDb<LocalId> {
        &self.locals
    }

    fn locals_mut(&mut self) -> &mut EntityDb<LocalId> {
        &mut self.locals
    }

    fn local_dbgs(&self) -> &SparseMap<LocalId, LocalDbg> {
        &self.local_dbgs
    }

    fn local_dbgs_mut(&mut self) -> &mut SparseMap<LocalId, LocalDbg> {
        &mut self.local_dbgs
    }
}

impl CtBody for Body {
    fn ct_blocks(&self) -> &EntityDb<Bb> {
        &self.comptime_bbs
    }

    fn ct_blocks_mut(&mut self) -> &mut EntityDb<Bb> {
        &mut self.comptime_bbs
    }
}

impl CrtBody for Body {
    fn blocks(&self) -> &EntityDb<Bb> {
        &self.bbs
    }

    fn blocks_mut(&mut self) -> &mut EntityDb<Bb> {
        &mut self.bbs
    }
}

/// Compile-Time Only SIR [`Body`].
///
/// # Note
///
/// Here because the comptime is implied by the fact that this is compile-time
/// only body, nothing is marked as `comptime`, but it behaves exactly as if
/// it were.
#[non_exhaustive]
#[derive(Debug, Clone)]
pub struct CtoBody {
    /// Locals
    pub locals: EntityDb<LocalId>,
    /// Local debug information
    pub local_dbgs: SparseMap<LocalId, LocalDbg>,
    /// Compile-time only basic blocks
    pub bbs: EntityDb<Bb>,
    /// When set to `true` if the cto-body contains no locals, no debug infos, and
    /// one basic-block with only a `Ret` terminator, it will [`PrettyDump`] it with
    /// nothing `""`.
    ///
    /// Otherwise if `false` it will always print the block.
    ///
    /// [`PrettyDump`]: lunc_utils::pretty::PrettyDump
    pub optional: bool,
}

impl CtoBody {
    fn empty(optional: bool) -> CtoBody {
        CtoBody {
            locals: EntityDb::new(),
            local_dbgs: SparseMap::new(),
            bbs: EntityDb::new(),
            optional,
        }
    }

    /// Create a new empty cto-body with `%RET: UNKNOWN`.
    pub fn new(optional: bool) -> CtoBody {
        let mut body = CtoBody::empty(optional);

        body.new_local(Comptime::No, Mutability::Mut, Type::dummy());

        body
    }

    /// Create a cto-body with `%RET: void`.
    pub fn with_ret(optional: bool) -> CtoBody {
        let mut body = CtoBody::empty(optional);

        body.new_local(
            Comptime::No,
            Mutability::Mut,
            Type::PrimType(PrimType::Void),
        );

        body
    }

    /// Is this block empty ? (described in [`CtoBody`] docs)
    pub fn is_empty(&self) -> bool {
        self.locals.count() <= 1
            && self.local_dbgs.is_empty()
            && self
                .bbs
                .try_get(Bb::new(0))
                .is_some_and(|bb| bb.stmts.is_empty() && *bb.term() == Terminator::Return)
    }

    /// Create a [`SirBuilder`] for the basic-blocks.
    ///
    /// [`SirBuilder`]: crate::builder::SirBuilder
    pub fn builder<'body>(&'body mut self) -> CtBuilder<'body> {
        todo!();
    }
}

impl LocalAble for CtoBody {
    fn locals(&self) -> &EntityDb<LocalId> {
        &self.locals
    }

    fn locals_mut(&mut self) -> &mut EntityDb<LocalId> {
        &mut self.locals
    }

    fn local_dbgs(&self) -> &SparseMap<LocalId, LocalDbg> {
        &self.local_dbgs
    }

    fn local_dbgs_mut(&mut self) -> &mut SparseMap<LocalId, LocalDbg> {
        &mut self.local_dbgs
    }
}

impl CtBody for CtoBody {
    fn ct_blocks(&self) -> &EntityDb<Bb> {
        &self.bbs
    }

    fn ct_blocks_mut(&mut self) -> &mut EntityDb<Bb> {
        &mut self.bbs
    }
}

/// A function definition
///
/// ```text
/// "<" path ">" :: fun({TMP: TYPE}) -> TYPE {
///     { comptime? mut? ident: TYPE; } // user-defined bindings with their type
///     { comptime? TMP: TYPE; }        // compiler generated temporary
///     { comptime? BASIC_BLOCK }       // control-flow graph
/// }
/// ```
///
/// # Note
///
/// A function definition MUST have an entry point that is not comptime.
///
/// A [`Fundef`] should be created using [`Fundef::new`].
#[non_exhaustive]
#[derive(Debug, Clone)]
pub struct Fundef {
    /// Absolute path of the fundef
    pub path: Path,
    /// Function parameters
    pub params: Vec<Param>,
    /// Function return type
    pub ret: Type,
    /// Is the signature finished?
    pub(crate) sig_finished: bool,
    /// Body of the function
    pub body: Body,
}

impl Fundef {
    /// Create a new function definition with the provided path, and with the
    /// DSIR params.
    ///
    /// # Note
    ///
    /// The created function have [`Type::dummy()`] has type for every created
    /// parameter and the return type. Translation isn't performed.
    pub fn new(path: Path, params: &[DsParam]) -> Fundef {
        let mut locals = EntityDb::new();
        let mut local_dbgs = SparseMap::new();

        // register the %RET local
        locals.create(Local {
            comptime: Comptime::No,
            id: LocalId::new(0),
            mutability: Mutability::Mut,
            typ: Type::dummy(),
        });

        // register the param locals
        let params_l = locals.create_many(
            |id, i| {
                local_dbgs.insert(
                    id,
                    LocalDbg {
                        id,
                        name: params[i].name.node.clone(),
                        kind: LocalKind::Param,
                        loc: params[i].loc.clone().unwrap(),
                    },
                );

                Local {
                    comptime: Comptime::No,
                    id,
                    mutability: Mutability::Not,
                    typ: Type::dummy(),
                }
            },
            params.len(),
        );

        Fundef {
            path,
            params: params_l
                .iter()
                .map(|id| Param {
                    local: *id,
                    typ: Type::dummy(),
                })
                .collect(),
            ret: Type::dummy(),
            sig_finished: false,
            body: Body {
                locals,
                local_dbgs,
                comptime_bbs: EntityDb::new(),
                bbs: EntityDb::new(),
            },
        }
    }

    #[track_caller]
    fn assert_sig_not_finished(&self) {
        if self.sig_finished {
            panic!("expected the signature of the function to not be finished.");
        }
    }

    /// Set the `nth` parameter of the function to type `typ`.
    #[track_caller]
    pub fn set_param_type(&mut self, nth: usize, typ: Type) {
        self.assert_sig_not_finished();

        self.params.get_mut(nth).expect("valid parameter index").typ = typ;
    }

    /// Set the type of `ret`.
    #[track_caller]
    pub fn set_ret(&mut self, typ: Type) {
        self.assert_sig_not_finished();

        self.body.get_local_mut(LocalId::RET).typ = typ.clone();
        self.ret = typ;
    }

    /// Mark the signature of the function to be finished.
    #[track_caller]
    pub fn finish_sig(&mut self) {
        self.assert_sig_not_finished();

        if self.params.iter().any(|param| param.typ.is_dummy()) || self.ret.is_dummy() {
            panic!(
                "function param type or return type cannot be the dummy type after the signature is marked as finished"
            );
        }

        self.sig_finished = true;
    }

    /// Creates a builder for the run-time basic-blocks.
    pub fn builder<'body>(&'body mut self) -> RtBuilder<'body> {
        self.body.builder()
    }

    /// Creates a builder for the compile-time basic-blocks.
    pub fn ct_builder<'body>(&'body mut self) -> CtBuilder<'body> {
        self.body.ct_builder()
    }

    /// Get the function parameter at `idx`.
    pub fn param(&self, idx: usize) -> &Param {
        self.params.get(idx).expect("invalid parameter index")
    }
}

/// Id of a [`Local`].
///
/// # Textual representation
///
/// A local can be represented in three ways possible:
///
/// - the return local, it's always the local with id 0, represented like that:
///   `%RET`.
/// - a local with debug information (like a binding definition or a function
///   parameter), it is represented like that `%NAME` with `NAME` being the name
///   in the debug infos.
/// - otherwise, represented like that `%NN` with `NN` being the id of the
///   local, in this case the local was generated by the compiler.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct LocalId(u32);

impl LocalId {
    /// The `%RET` local.
    pub const RET: LocalId = LocalId(0);
}

entity!(LocalId, Local);

/// A Local.
#[derive(Debug, Clone)]
pub struct Local {
    /// Compile-time known?
    pub comptime: Comptime,
    /// Id of this local.
    pub id: LocalId,
    /// Is it mutable?
    pub mutability: Mutability,
    /// Type of the local
    pub typ: Type,
}

/// What kind of local it is?
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum LocalKind {
    /// The local was a binding definition statement
    Binding,
    /// The local was a function parameter
    Param,
}

/// Debug information for a [`Local`].
#[derive(Debug, Clone)]
pub struct LocalDbg {
    /// Id of the local that this debug infos are attached to.
    pub id: LocalId,
    /// Name of the local
    pub name: String,
    /// Kind of the local
    pub kind: LocalKind,
    /// Location of the whole piece of code defining it.
    ///
    /// e.g: `a := 2;`, `mut b := 3;`, `let a: u32;`, `param: u32`
    pub loc: Span,
}

/// Function parameter
#[derive(Debug, Clone)]
pub struct Param {
    pub local: LocalId,
    pub typ: Type,
}

impl Param {
    /// Create a [`PValue`] from this parameter.
    pub fn pvalue(&self) -> PValue {
        PValue::Local(self.local)
    }
}

/// Id of a [`BasicBlock`].
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Bb(u32);

entity!(Bb, BasicBlock);

/// Basic block, shortened to: `bb`.
///
/// A basic block is a node of the CFG nature of SIR, branching (the edges)
/// occurs between basic-blocks. A basic-block is a sequence of statements
/// followed by a terminator at the end.
///
/// A basic-block has only one entry-point (the first statement kinda), and the
/// terminator always branches to another BB or something else.
///
/// Basic blocks are numbered like temporaries are, the first bb, the entry has
/// the id 0 and name `BB0` the second, `BB1`. Basic-block ids are not shared
/// between compile-time and runtime basic blocks, so we can have `comptime BB1`
/// and `BB1` and they do not refer to the same basic block. For convenience
/// the first basic block is always the entry block and is annotated like that:
/// `@entry BB0: { ... }`, and as said before you can have two `BB0` one runtime
/// and one comptime. So a function MUST have an entry basic block and may also
/// have a `comptime @entry BB0: { ... }`.
#[derive(Debug, Clone)]
pub struct BasicBlock {
    /// Id of this bb, gives the name to the BB: `BBxx` where `xx` is the id.
    pub id: Bb,
    /// Is this bb comptime?
    pub comptime: Comptime,
    /// Statements contained in the bb.
    pub stmts: Vec<Statement>,
    /// Terminator of the basic block
    ///
    /// # Note
    ///
    /// It should only be `None` when we first construct the block.
    pub term: Option<Terminator>,
}

impl BasicBlock {
    /// Get the terminator of the basic-block.
    #[track_caller]
    pub fn term(&self) -> &Terminator {
        self.term.as_ref().expect("unterminated basic-block")
    }
}

/// Statement -- performs some computation.
#[derive(Debug, Clone, PartialEq)]
pub enum Statement {
    /// `PVALUE = RVALUE`
    ///
    /// Firsts evaluates the `RVALUE` (right value, of the assignment) and
    /// stores the result in `PVALUE` (place value), which must represent a
    /// memory location with a suitable type.
    Assignment(PValue, RValue),
}

/// Terminator -- edges of the CFG.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Terminator {
    /// `goto(BB)`
    ///
    /// Normal control-flow, "jumps" to basic-block `BB`.
    Goto(Bb),
    /// `if PVALUE { BB0 } else { BB1 }` *where `BB0` is `.1` and `BB1` is `.2`*
    ///
    /// Evaluates `PVALUE`, branches to `BB0` if it's `true` or to `BB1`
    /// otherwise.
    If(PValue, Bb, Bb),
    /// `return`
    ///
    /// Return to the caller.
    ///
    /// # Note
    ///
    /// When using `return` the `%RET` temporary `MUST` be initialized, even
    /// when the return type of the function is a ZST, then you initialize it
    /// like that: `%RET = nothing;`. Only function that has `never` has return
    /// type will not initialize `%RET`, because they do not use the `Return`
    /// terminator.
    Return,
    /// `unreachable`
    ///
    /// The control-flow cannot reach this because a previous statement already
    /// stopped the control-flow, with a call to a function with type `never`
    /// for example.
    Unreachable,
}

/// Place value -- a memory location with an appropriate type.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum PValue {
    /// `LOCAL`
    ///
    /// A reference to a local
    Local(LocalId),
    /// `<path>`
    ///
    /// Reference to an `Item`
    Item(ItemId),
    /// `PVALUE.*`
    ///
    /// Dereference a pointer.
    Deref(Box<PValue>),
}

/// Comptime Value -- representation of the value of an expression known at
/// compile-time.
#[derive(Debug, Clone, PartialEq)]
pub enum CValue {
    /// `true` / `false`
    ///
    /// A boolean value of type `bool`.
    Bool(bool),
    /// A type, in Lun types are first-class citizens.
    ///
    /// As type `type`.
    Type(Type),
    /// 8 bit signed integer.
    I8(i8),
    /// 16 bit signed integer.
    I16(i16),
    /// 32 bit signed integer.
    I32(i32),
    /// 64 bit signed integer.
    I64(i64),
    /// 128 bit signed integer.
    I128(i128),
    /// Pointer-sized signed integer.
    ///
    /// Create it with the `Value::isz16`, `Value::isz32` and `Value::isz64`
    /// functions.
    Isz(i64),
    /// 8 bit unsigned integer.
    U8(u8),
    /// 16 bit unsigned integer.
    U16(u16),
    /// 32 bit unsigned integer.
    U32(u32),
    /// 64 bit unsigned integer.
    U64(u64),
    /// 128 bit unsigned integer.
    U128(u128),
    /// Pointer-sized unsigned integer.
    ///
    /// Create it with the `Value::usz16`, `Value::usz32` and `Value::usz64`
    /// functions.
    Usz(u64),
    /// IEEE-754 32 bit floating point number
    F32(f32),
    /// IEEE-754 64 bit floating point number
    F64(f64),
    /// a string literal
    ///
    /// A value of type `*str`.
    Str(Box<str>),
    /// a c-string literal
    ///
    /// A value of type `*i8`
    CStr(Box<str>),
    /// a unicode codepoint
    ///
    /// Internally equivalent to a `u32`.
    Char(char),
    /// `nothing`
    ///
    /// A value of type every type that is a Zero Sized Type, used to initialize
    /// the `%RET` before returning.
    ///
    /// # Note
    ///
    /// In practice this value is a no-op, it's just used to ensure everything
    /// used is initialized.
    Nothing,
}

impl CValue {
    /// Create a new [`CValue::Usz`] from a 16-bit integer.
    pub fn usz16(u: u16) -> CValue {
        CValue::Usz(u as u64)
    }

    /// Create a new [`CValue::Usz`] from a 32-bit integer.
    pub fn usz32(u: u32) -> CValue {
        CValue::Usz(u as u64)
    }

    /// Create a new [`CValue::Usz`] from a 64-bit integer.
    pub fn usz64(u: u64) -> CValue {
        CValue::Usz(u)
    }
    /// Create a new [`CValue::Isz`] from a 16-bit integer.
    pub fn isz16(i: i16) -> CValue {
        CValue::Isz(i as i64)
    }

    /// Create a new [`CValue::Isz`] from a 32-bit integer.
    pub fn isz32(i: i32) -> CValue {
        CValue::Isz(i as i64)
    }

    /// Create a new [`CValue::Isz`] from a 64-bit integer.
    pub fn isz64(i: i64) -> CValue {
        CValue::Isz(i)
    }
}

impl From<bool> for CValue {
    fn from(value: bool) -> Self {
        CValue::Bool(value)
    }
}

impl From<u8> for CValue {
    fn from(value: u8) -> Self {
        CValue::U8(value)
    }
}

impl From<u16> for CValue {
    fn from(value: u16) -> Self {
        CValue::U16(value)
    }
}

impl From<u32> for CValue {
    fn from(value: u32) -> Self {
        CValue::U32(value)
    }
}

impl From<u64> for CValue {
    fn from(value: u64) -> Self {
        CValue::U64(value)
    }
}

impl From<u128> for CValue {
    fn from(value: u128) -> Self {
        CValue::U128(value)
    }
}

impl From<i8> for CValue {
    fn from(value: i8) -> Self {
        CValue::I8(value)
    }
}

impl From<i16> for CValue {
    fn from(value: i16) -> Self {
        CValue::I16(value)
    }
}

impl From<i32> for CValue {
    fn from(value: i32) -> Self {
        CValue::I32(value)
    }
}

impl From<i64> for CValue {
    fn from(value: i64) -> Self {
        CValue::I64(value)
    }
}

impl From<i128> for CValue {
    fn from(value: i128) -> Self {
        CValue::I128(value)
    }
}

impl From<f32> for CValue {
    fn from(value: f32) -> Self {
        CValue::F32(value)
    }
}

impl From<f64> for CValue {
    fn from(value: f64) -> Self {
        CValue::F64(value)
    }
}

impl From<char> for CValue {
    fn from(value: char) -> Self {
        CValue::Char(value)
    }
}

/// Right value -- a computation that outputs a result. This result must be
/// stored in a memory location, so inside of a `PVALUE`.
///
/// The SIR is sequential so it doesn't contain nested expressions: everything
/// is flattened out, that's why we need temporaries.
#[derive(Debug, Clone, PartialEq)]
pub enum RValue {
    /// `CVALUE`
    ///
    /// A constant value.
    CValue(CValue),
    /// `use(PVALUE)`
    ///
    /// Reads a `PVALUE`
    Use(PValue),
    /// `& mut? PVALUE`
    ///
    /// Takes a pointer to `PVALUE`
    Borrow(Mutability, PValue),
    /// `PVALUE as TYPE`
    ///
    /// A primitive cast of `PVALUE` to type `TYPE`.
    Cast(PValue, Type),
    /// `PVALUE0 <binop> PVALUE1` *where `PVALUE0` is `.0`, and `PVALUE1` is
    /// `.2`*
    ///
    /// Binary operation between the two `PVALUE`s, evaluates `PVALUE0` first,
    /// then `PVALUE1`.
    Binary(PValue, BinOp, PValue),
    /// `<unop> PVALUE`
    ///
    /// Unary operation on `PVALUE`.
    Unary(UnOp, PValue),
    /// `call(PVALUE0, (PVALUE1..))`
    ///
    /// Calls the function `PVALUE0` with `PVALUE1..` as arguments
    Call { callee: PValue, args: Vec<PValue> },
}

/// Binary operation, subset of [`lunc_ast::BinOp`].
///
/// # Note
///
/// This is a subset because it does not contain the short-circuiting operations
/// like `LogicalAnd` & `LogicalOr`.
#[derive(Debug, Clone, PartialEq)]
pub enum BinOp {
    /// Addition, +
    Add,
    /// Subtraction, -
    Sub,
    /// Multiplication, *
    Mul,
    /// Division, /
    Div,
    /// Remainder, %
    Rem,
    /// Less than, <
    CompLT,
    /// Less than or equal, <=
    CompLE,
    /// Greater than, >
    CompGT,
    /// Greater than or equal, >=
    CompGE,
    /// Equal, ==
    CompEq,
    /// Not equal, !=
    CompNe,
    /// Assignment, =
    Assignment,
    /// Bitwise and, &
    And,
    /// Bitwise xor, ^
    Xor,
    /// Bitwise or, |
    Or,
    /// Shift right, >>
    Shr,
    /// Shift left, <<
    Shl,
}

impl BinOp {
    /// Returns the equivalent operator
    pub fn op_str(&self) -> &'static str {
        match self {
            BinOp::Add => "+",
            BinOp::Sub => "-",
            BinOp::Mul => "*",
            BinOp::Div => "/",
            BinOp::Rem => "%",
            BinOp::CompLT => "<",
            BinOp::CompLE => "<=",
            BinOp::CompGT => ">",
            BinOp::CompGE => ">=",
            BinOp::CompEq => "==",
            BinOp::CompNe => "!=",
            BinOp::Assignment => "=",
            BinOp::And => "&",
            BinOp::Xor => "^",
            BinOp::Or => "|",
            BinOp::Shr => ">>",
            BinOp::Shl => "<<",
        }
    }
}

/// Unary Operations, a subset of [`lunc_ast::UnOp`]
///
/// # Note
///
/// This is a subset because it does not contain the `Dereference` unary because
/// it is part of `PVALUE`.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum UnOp {
    /// `- expression`
    Negation,
    /// `! expression`
    Not,
}

impl UnOp {
    /// Returns the equivalent operator.
    pub fn op_str(&self) -> &'static str {
        match self {
            UnOp::Negation => "-",
            UnOp::Not => "!",
        }
    }
}

/// A function declaration
///
/// ```text
/// "<" path ">" :: extern "ABI" name "NAME" fun({TMP: TYPE}) -> TYPE;
/// // here ABI, is for now one of: C, Lun
/// // and NAME, before link_name is the name of the function declaration to look for.
/// ```
#[non_exhaustive]
#[derive(Debug, Clone)]
pub struct Fundecl {
    /// Absolute path of the fundecl
    pub path: Path,
    /// Abi
    pub abi: Abi,
    /// Name of the symbol to declare
    pub name: String,
    /// Function parameters
    pub params: Vec<Type>,
    /// Function return type
    pub ret: Type,
    /// Body, used to hold the type-expression SIR.
    ///
    /// The `%RET` local always has `void` type.
    pub body: CtoBody,
}

impl Fundecl {
    /// Create a new function declaration, without params and a dummy return
    /// type.
    pub fn new(path: Path, abi: Abi, name: String) -> Fundecl {
        Fundecl {
            path,
            abi,
            name,
            params: Vec::new(),
            ret: Type::dummy(),
            body: CtoBody::with_ret(true),
        }
    }
}

/// A global uninit
///
/// ```text
/// "<" path ">" : TYPE, name "NAME";
/// ```
#[non_exhaustive]
#[derive(Debug, Clone)]
pub struct GlobalUninit {
    /// Absolute path of the global uninit
    pub path: Path,
    /// Type of the Global.
    pub typ: Type,
    /// Name of the symbol to declare
    pub name: String,
    /// Body, used to hold the type-expression SIR.
    ///
    /// The `%RET` local always has `void` type.
    pub body: CtoBody,
}

impl GlobalUninit {
    /// Create a new global uninit with a dummy type.
    pub fn new(path: Path, name: String) -> GlobalUninit {
        GlobalUninit {
            path,
            typ: Type::dummy(),
            name,
            body: CtoBody::with_ret(true),
        }
    }
}

/// A global definition
///
/// ```text
/// "<" path ">" : TYPE = {
///     { mut? ident: TYPE; }  // user-defined bindings with their type
///     { tmp TMP: TYPE; }     // compiler generated temporary
///     { BASIC_BLOCK }        // control-flow graph
/// }
/// ```
///
/// Global definitions are compiled the same way functions are compiled, but
/// basic-block are ALWAYS comptime, the `%RET` temporary contains the final
/// result after compile-time evaluation and the `Return` terminator does not
/// "return to the caller", but indicates to the compile-time evaluator that the
/// evaluation has terminated.
///
/// # Note
///
/// *Please note that the global-defs are run at COMPILE-TIME, there is no "life
/// before main" shenanigans.*
#[non_exhaustive]
#[derive(Debug, Clone)]
pub struct GlobalDef {
    /// Absolute path of the global uninit
    pub path: Path,
    /// Type of the Global.
    pub typ: Type,
    /// Body
    pub body: CtoBody,
}

impl GlobalDef {
    /// Create a new global-def
    pub fn new(path: Path) -> GlobalDef {
        let body = CtoBody::new(false);

        GlobalDef {
            path,
            typ: Type::dummy(),
            body,
        }
    }
}

/// SIR type.
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
    /// A local that has "type" `Type`.
    Local(LocalId),
    /// A reference to an item with "type" `Type`.
    Item(ItemId),
}

impl Type {
    /// Dummy type, used when the type is not yet known, used when we convert
    /// from the DSIR to SIR, should not be present anymore after type-checking.
    pub const fn dummy() -> Type {
        Type::Item(ItemId::RESERVED)
    }

    /// Is this type the [dummy] type?
    ///
    /// [dummy]: Type::dummy
    #[inline(always)]
    pub fn is_dummy(&self) -> bool {
        *self == Type::dummy()
    }
}

/// Primitive types of Lun.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum PrimType {
    /// Signed pointer-size integer
    Isz,
    /// Signed 128-bit integer
    I128,
    /// Signed 64-bit integer
    I64,
    /// Signed 32-bit integer
    I32,
    /// Signed 16-bit integer
    I16,
    /// Signed 8-bit integer
    I8,
    /// Unsigned pointer-size integer
    Usz,
    /// Unsigned 128-bit integer
    U128,
    /// Unsigned 64-bit integer
    U64,
    /// Unsigned 32-bit integer
    U32,
    /// Unsigned 16-bit integer
    U16,
    /// Unsigned 8-bit integer
    U8,
    /// 128-bit IEEE 754-2008, float
    F128,
    /// 64-bit IEEE 754-2008, float
    F64,
    /// 32-bit IEEE 754-2008, float
    F32,
    /// 16-bit IEEE 754-2008, float
    F16,
    /// Boolean, `true`/`false`
    Bool,
    /// String slice DST type
    ///
    /// # Note
    ///
    /// DSTs are not yet implemented so this type is not working for now.
    Str,
    /// 32-bit integer representing a Unicode Codepoint.
    Char,
    /// ZST, this type indicates that the control flow is stopped after the
    /// evaluation of an expression of this type.
    Never,
    /// ZST, nothing to return
    Void,
    /// Types in Lun are first-class citizen, so here's the "type" of types.
    Type,
}

impl Display for PrimType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            PrimType::Isz => write!(f, "isz"),
            PrimType::I128 => write!(f, "i128"),
            PrimType::I64 => write!(f, "i64"),
            PrimType::I32 => write!(f, "i32"),
            PrimType::I16 => write!(f, "i16"),
            PrimType::I8 => write!(f, "i8"),
            PrimType::Usz => write!(f, "usz"),
            PrimType::U128 => write!(f, "u128"),
            PrimType::U64 => write!(f, "u64"),
            PrimType::U32 => write!(f, "u32"),
            PrimType::U16 => write!(f, "u16"),
            PrimType::U8 => write!(f, "u8"),
            PrimType::F128 => write!(f, "f128"),
            PrimType::F64 => write!(f, "f64"),
            PrimType::F32 => write!(f, "f32"),
            PrimType::F16 => write!(f, "f16"),
            PrimType::Bool => write!(f, "bool"),
            PrimType::Str => write!(f, "str"),
            PrimType::Char => write!(f, "char"),
            PrimType::Never => write!(f, "never"),
            PrimType::Void => write!(f, "void"),
            PrimType::Type => write!(f, "type"),
        }
    }
}
