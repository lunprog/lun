//! Sequential Intermediate Representation of Lun.
#![doc(
    html_logo_url = "https://raw.githubusercontent.com/lunprog/lun/main/src/assets/logo_no_bg_black.png"
)]

pub mod pretty;

use std::io::{self, Write};

use lunc_ast::{Abi, Comptime, Mutability, Path};
use lunc_entity::{EntityDb, entity};
use lunc_utils::Span;

/// A Lun orb.
#[derive(Debug, Clone)]
pub struct Orb {
    pub items: EntityDb<ItemId>,
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
}

impl Item {
    /// Returns the path of the item.
    pub fn path(&self) -> &Path {
        match self {
            Self::Fundef(fundef) => &fundef.path,
            Self::Fundecl(fundecl) => &fundecl.path,
        }
    }
}

/// SIR body, contains the temporaries, user-bindings and basic blocks of a
/// function defintion or a global definition
#[derive(Debug, Clone)]
pub struct Body {
    /// User-defined bindings
    pub bindings: EntityDb<BindingId>,
    /// temporaries
    pub temporaries: EntityDb<Tmp>,
    /// compile-time only basic blocks
    pub comptime_bbs: EntityDb<Bb>,
    /// basic-blocks.
    pub bbs: EntityDb<Bb>,
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
#[derive(Debug, Clone)]
pub struct Fundef {
    /// Absolute path of the fundef
    pub path: Path,
    /// Function parameters
    pub params: Vec<Param>,
    /// Function return type
    pub ret: Type,
    /// Body of the function
    pub body: Body,
}

/// Id of a [`Binding`].
///
/// Represented by the name of the binding.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct BindingId(u32);

entity!(BindingId, Binding);

/// User-defined binding.
#[derive(Debug, Clone)]
pub struct Binding {
    /// Compile-time?
    pub comptime: Comptime,
    /// Is it mutable?
    pub mutability: Mutability,
    /// Name of the binding
    pub name: String,
    /// Type of the binding
    pub typ: Type,
    /// Location of the whole statement defining it
    ///
    /// e.g: `a := 2;`, `mut b := 3;`, `let a: u32;`
    pub loc: Span,
}

/// Id of a [`Temporary`].
///
/// Represented like so `%NN` where `NN` is the Id but if `id == 0` then it is
/// represented like so: `%RET`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Tmp(u32);

entity!(Tmp, Temporary);

/// A temporary.
#[derive(Debug, Clone)]
pub struct Temporary {
    pub id: Tmp,
    pub comptime: Comptime,
    pub typ: Type,
}

/// Function parameter
#[derive(Debug, Clone)]
pub struct Param {
    pub tmp: Tmp,
    pub typ: Type,
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
    /// Terminator of the
    pub term: Terminator,
}

/// Statement -- performs some computation.
#[derive(Debug, Clone)]
pub enum Statement {
    /// `PVALUE = RVALUE`
    ///
    /// Firsts evaluates the `RVALUE` (right value, of the assignment) and
    /// stores the result in `PVALUE` (place value), which must represent a
    /// memory location with a suitable type.
    Assignment(PValue, RValue),
}

/// Terminator -- edges of the CFG.
#[derive(Debug, Clone)]
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
    Return,
    /// `unreachable`
    ///
    /// The control-flow cannot reach this because a previous statement already
    /// stopped the control-flow, with a call to a function with type `never`
    /// for example.
    Unreachable,
}

/// Place value -- a memory location with an appropriate type.
#[derive(Debug, Clone)]
pub enum PValue {
    /// `BINDING`
    ///
    /// A reference to a user-binding
    Binding(BindingId),
    /// `TEMP`
    ///
    /// A reference to a temporary
    Tmp(Tmp),
    /// `<path>`
    ///
    /// Reference to an `Item`
    Item(ItemId),
    /// `PVALUE.*`
    ///
    /// Dereference a pointer.
    Deref(Box<PValue>),
}

/// Right value -- a computation that outputs a result. This result must be
/// stored in a memory location, so inside of a `PVALUE`.
///
/// The SIR is sequential so it doesn't contain nested expressions: everything
/// is flattened out, that's why we need temporaries.
#[derive(Debug, Clone)]
pub enum RValue {
    /// `use(PVALUE)`
    ///
    /// reads a `PVALUE`
    Use(PValue),
    /// `& mut? PVALUE`
    ///
    /// Takes a pointer to `PVALUE`
    Borrow(Mutability, PValue),
    /// `12`, `57`, `69`
    ///
    /// Unsigned integer immediate.
    Uint(Int),
    /// `-12`, `34`, `-69`
    ///
    /// Signed integer immediate.
    Sint(Int),
    /// `6.9`, `-1.602e-19`..
    ///
    /// Float immediate
    Float(Float),
    /// `true` / `false`
    ///
    /// Boolean immediate
    Bool(bool),
    /// a string literal, (`.0`), and its tag (`.1`)
    String(String, Option<String>),
    /// a primitive type, because types in Lun are first-class citizens.
    PrimitiveType(PrimitiveType),
    /// `PVALUE as TYPE`
    ///
    /// a primitive cast of `PVALUE` to type `TYPE`.
    Cast(PValue, Type),
    /// `PVALUE0 <binop> PVALUE1` *where `PVALUE0` is `.0`, and `PVALUE1` is
    /// `.2`*
    ///
    /// binary operation between the two `PVALUE`s, evaluates `PVALUE0` first,
    /// then `PVALUE1`.
    Binary(PValue, BinOp, PValue),
    /// `<unop> PVALUE`
    ///
    /// unary operation on `PVALUE`.
    Unary(UnOp, PValue),
    /// `call(PVALUE0, (PVALUE1..))`
    ///
    /// Calls the function `PVALUE0` with `PVALUE1..` as arguments
    Call { callee: PValue, args: Vec<PValue> },
}

/// An immediate integer value, doesn't have a signedness associated to it.
#[derive(Debug, Clone)]
pub enum Int {
    /// 8-bit
    Int8(u8),
    /// 16-bit
    Int16(u16),
    /// 32-bit
    Int32(u32),
    /// 64-bit
    Int64(u64),
    /// 128-bit
    Int128(u128),
    /// *pointer-size*-bit
    IntSz(u128),
}

impl Int {
    /// Write the [`Int`] like if it was unsigned.
    pub fn write_as_string_unsigned(&self, w: &mut dyn Write) -> io::Result<()> {
        match self {
            Self::Int8(u) => write!(w, "{u}"),
            Self::Int16(u) => write!(w, "{u}"),
            Self::Int32(u) => write!(w, "{u}"),
            Self::Int64(u) => write!(w, "{u}"),
            Self::Int128(u) => write!(w, "{u}"),
            Self::IntSz(u) => write!(w, "{u}"),
        }
    }

    /// Write the [`Int`] like if it was signed.
    pub fn write_as_string_signed(&self, w: &mut dyn Write) -> io::Result<()> {
        match self {
            Self::Int8(u) => {
                let i = u.cast_signed();
                write!(w, "{i}")
            }
            Self::Int16(u) => {
                let i = u.cast_signed();
                write!(w, "{i}")
            }
            Self::Int32(u) => {
                let i = u.cast_signed();
                write!(w, "{i}")
            }
            Self::Int64(u) => {
                let i = u.cast_signed();
                write!(w, "{i}")
            }
            Self::Int128(u) => {
                let i = u.cast_signed();
                write!(w, "{i}")
            }
            Self::IntSz(u) => {
                let i = u.cast_signed();
                write!(w, "{i}")
            }
        }
    }
}

/// An immediate float value, IEEE 754-2008 compliant.
#[derive(Debug, Clone)]
pub enum Float {
    F16(u16),
    F32(f32),
    F64(f64),
    F128(u128),
}

impl Float {
    /// Write the [`Float`].
    pub fn write(&self, w: &mut dyn Write) -> io::Result<()> {
        match self {
            Self::F16(f) => write!(w, "{f:+e}"),
            Self::F32(f) => write!(w, "{f:+e}"),
            Self::F64(f) => write!(w, "{f:+e}"),
            Self::F128(f) => write!(w, "{f:+e}"),
        }
    }
}

/// Binary operation, subset of [`lunc_ast::BinOp`].
///
/// # Note
///
/// This is a subset because it does not contain the short-circuiting operations
/// like `LogicalAnd` & `LogicalOr`.
#[derive(Debug, Clone)]
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
}

/// SIR type.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub enum Type {
    /// The type is not known, used when we convert the DSIR to SIR, should not
    /// be present anymore after type-checking.
    #[default]
    Unknown,
    /// primitive type
    PrimitiveType(PrimitiveType),
    /// a pointer
    Ptr(Mutability, Box<Type>),
    /// a function pointer
    Funptr(Vec<Type>, Box<Type>),
    /// a temporary that has "type" `Type`.
    Tmp(Tmp),
    /// a reference to an item with "type" `Type`.
    Item(ItemId),
}

/// Primitive types of SIR.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum PrimitiveType {
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
