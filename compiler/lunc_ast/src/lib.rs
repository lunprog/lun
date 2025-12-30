//! Ast types shared across compiler stages.
#![doc(
    html_logo_url = "https://raw.githubusercontent.com/lunprog/lun/main/src/assets/logo_no_bg_black.png"
)]

use std::{
    fmt::Display,
    io::{self, Write},
    str::FromStr,
};

use lunc_token::TokenType;
use lunc_utils::{
    Span,
    pretty::{PrettyCtxt, PrettyDump},
};
use serde::{Deserialize, Serialize};

/// A 'Path' is a name in Lun, like `orb`, `hello`, `core::panic`, ..
///
/// It is composed of segments of path, identifiers or orb.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Deserialize, Serialize)]
pub struct Path {
    segments: Vec<PathSegment>,
}

impl Path {
    /// Creates a new empty path
    pub const fn new() -> Path {
        Path {
            segments: Vec::new(),
        }
    }

    /// Creates a new path with just a single segment
    pub fn with_root(root: impl Into<PathSegment>) -> Path {
        Path {
            segments: vec![root.into()],
        }
    }

    /// Returns the amount of members in the path eg:
    ///
    /// `orb`               -> 1
    /// `hello`             -> 1
    /// `orb::main`         -> 2
    /// `std::panic::Panic` -> 3
    /// etc..
    pub fn len(&self) -> usize {
        self.segments.len()
    }

    /// Is the path empty?
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Returns a slice of the underlying path
    pub fn as_slice(&self) -> &[PathSegment] {
        &self.segments
    }

    /// Returns a mutable reference to the last segment of the path
    ///
    /// # Example
    ///
    /// `orb`        -> mut ref to `orb`
    /// `orb::driver` -> mut ref to `driver`
    /// *etc..*
    pub fn last_mut(&mut self) -> Option<&mut PathSegment> {
        self.segments.last_mut()
    }

    /// Returns a reference to the last segment of the path
    pub fn last(&self) -> Option<&PathSegment> {
        self.segments.last()
    }

    /// Returns a reference to the first segment of the path
    pub fn first(&self) -> Option<&PathSegment> {
        self.segments.first()
    }

    /// Returns a mutable reference to the first segment of the path
    pub fn first_mut(&mut self) -> Option<&mut PathSegment> {
        self.segments.first_mut()
    }

    /// Push a new segment to the path
    ///
    /// # Panic
    ///
    /// This function panics if you push a [`PathSegment::Orb`] if it's not the
    /// first segment of the path.
    pub fn push_seg(&mut self, segment: impl Into<PathSegment>) {
        let seg = segment.into();

        if !self.is_empty() && seg == PathSegment::Orb {
            panic!("pushed a 'orb' segment not as the first segment of a path")
        }

        self.segments.push(seg)
    }

    /// Push an ident segment
    pub fn push(&mut self, ident: String) {
        if ident.as_str() == "orb" && self.is_empty() {
            self.segments.push(PathSegment::Orb);

            return;
        }
        self.segments.push(PathSegment::Ident(ident));
    }

    /// Pops the last member of the path and returns it
    pub fn pop(&mut self) -> Option<PathSegment> {
        self.segments.pop()
    }

    /// Is this path the root path? returns true if the path is equal to `orb`,
    /// false otherwise.
    pub fn is_root(&self) -> bool {
        self.segments == [PathSegment::Orb]
    }

    /// Append a path to this path
    pub fn append(&mut self, mut other: Path) {
        self.segments.append(&mut other.segments);
    }

    /// Converts this path to a vector of strings.
    pub fn to_string_vec(&self) -> Vec<String> {
        self.segments.iter().map(|seg| seg.to_string()).collect()
    }

    /// Does the path starts with a [`PathSegment::Orb`]?
    pub fn starts_with_orb(&self) -> bool {
        matches!(self.first(), Some(PathSegment::Orb))
    }

    /// Returns `true` if self == `_`
    pub fn is_underscore(&self) -> bool {
        self.len() == 1 && self.segments[0].is_ident_and(|id| id == "_")
    }

    /// Get the `i`th segment of the path.
    pub fn get(&self, i: usize) -> Option<&PathSegment> {
        self.segments.get(i)
    }
}

impl<S: ToString> FromIterator<S> for Path {
    /// Creates a new path from an iterator of strings, if the first thing is
    /// the string "orb" it will push an orb segment
    fn from_iter<T: IntoIterator<Item = S>>(iter: T) -> Self {
        let mut path = Path::new();

        for seg in iter {
            let seg_s = seg.to_string();
            path.push(seg_s);
        }

        path
    }
}

impl Default for Path {
    fn default() -> Self {
        Path::new()
    }
}

impl Display for Path {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if !self.is_empty() {
            write!(
                f,
                "{}",
                self.as_slice()
                    .iter()
                    .map(|seg| seg.to_string())
                    .collect::<Vec<_>>()
                    .join("::")
            )
        } else {
            write!(f, "∅")
        }
    }
}

impl<E> PrettyDump<E> for Path {
    fn try_dump(&self, ctx: &mut PrettyCtxt, _: &E) -> io::Result<()> {
        write!(ctx.out, "{self}")
    }
}

/// A segment of a path, `orb` or an identifier
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Deserialize, Serialize)]
pub enum PathSegment {
    /// Identifier segment like `abc`
    Ident(String),
    /// Orb starting segment `orb`, e.g: `orb::hello:world`, `orb` is a Orb
    /// segment.
    ///
    /// # Note
    ///
    /// This segment is only valid as the first segment of a [Path]
    Orb,
}

impl PathSegment {
    /// Returns `true` if `self` is `Ident(id)` and the value inside matches a
    /// predicate `f`.
    pub fn is_ident_and(&self, f: impl FnOnce(&str) -> bool) -> bool {
        match self {
            Self::Orb => false,
            Self::Ident(id) => f(id),
        }
    }
}

impl Display for PathSegment {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Ident(seg) => write!(f, "{seg}"),
            Self::Orb => write!(f, "orb"),
        }
    }
}

impl From<String> for PathSegment {
    fn from(value: String) -> Self {
        PathSegment::Ident(value)
    }
}

impl From<&str> for PathSegment {
    fn from(value: &str) -> Self {
        PathSegment::Ident(value.to_string())
    }
}

/// Binary operation.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum BinOp {
    /// addition
    Add,
    /// subtraction
    Sub,
    /// multiplication
    Mul,
    /// division
    Div,
    /// remainder
    Rem,
    /// less than
    CompLT,
    /// less than or equal
    CompLE,
    /// greater than
    CompGT,
    /// greater than or equal
    CompGE,
    /// equal
    CompEq,
    /// not equal
    CompNe,
    /// assignment
    Assignment,
    /// and
    LogicalAnd,
    /// or
    LogicalOr,
    /// &
    BitwiseAnd,
    /// ^
    BitwiseXor,
    /// |
    BitwiseOr,
    /// shift right, >>
    Shr,
    /// shift left, <<
    Shl,
}

impl Display for BinOp {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let str = match self {
            Self::Add => "+",
            Self::Sub => "-",
            Self::Mul => "*",
            Self::Div => "/",
            Self::Rem => "%",
            Self::CompLT => "<",
            Self::CompLE => "<=",
            Self::CompGT => ">",
            Self::CompGE => ">=",
            Self::CompEq => "==",
            Self::CompNe => "!=",
            Self::Assignment => "=",
            Self::LogicalAnd => "&&",
            Self::LogicalOr => "||",
            Self::BitwiseAnd => "&",
            Self::BitwiseXor => "^",
            Self::BitwiseOr => "|",
            Self::Shr => ">>",
            Self::Shl => "<<",
        };

        f.write_str(str)
    }
}

impl BinOp {
    pub fn from_tt(tt: &TokenType) -> Option<BinOp> {
        match tt {
            TokenType::Eq => Some(BinOp::Assignment),
            TokenType::Star => Some(BinOp::Mul),
            TokenType::Slash => Some(BinOp::Div),
            TokenType::Percent => Some(BinOp::Rem),
            TokenType::Plus => Some(BinOp::Add),
            TokenType::Minus => Some(BinOp::Sub),
            TokenType::Lt => Some(BinOp::CompLT),
            TokenType::Gt => Some(BinOp::CompGT),
            TokenType::LtEq => Some(BinOp::CompLE),
            TokenType::GtEq => Some(BinOp::CompGE),
            TokenType::EqEq => Some(BinOp::CompEq),
            TokenType::BangEq => Some(BinOp::CompNe),
            TokenType::And => Some(BinOp::BitwiseAnd),
            TokenType::AndAnd => Some(BinOp::LogicalAnd),
            TokenType::Caret => Some(BinOp::BitwiseXor),
            TokenType::Or => Some(BinOp::BitwiseOr),
            TokenType::OrOr => Some(BinOp::LogicalOr),
            TokenType::LtLt => Some(BinOp::Shl),
            TokenType::GtGt => Some(BinOp::Shr),
            _ => None,
        }
    }

    /// Is the binary operation rational? < <= > >= == !=
    pub fn is_relational(&self) -> bool {
        matches!(
            self,
            BinOp::CompLT
                | BinOp::CompLE
                | BinOp::CompGT
                | BinOp::CompGE
                | BinOp::CompEq
                | BinOp::CompNe
        )
    }

    pub fn is_logical(&self) -> bool {
        // TODO: implement logical operators like `"not" expr`, `expr "and"
        // expr`, `expr "or" expr`, `expr "xor" expr`
        matches!(self, Self::LogicalAnd | Self::LogicalOr)
    }
}

impl<E> PrettyDump<E> for BinOp {
    fn try_dump(&self, ctx: &mut PrettyCtxt, _: &E) -> io::Result<()> {
        write!(ctx.out, "{self:?}")
    }
}
/// Unary Operations
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum UnOp {
    // left unary operator
    /// `- expression`
    Negation,
    /// `! expression`
    Not,
    // right unary operator
    /// `expression.*`
    Dereference,
}

impl Display for UnOp {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let str = match self {
            Self::Negation => "-",
            Self::Not => "!",
            Self::Dereference => ".*",
        };

        f.write_str(str)
    }
}

impl UnOp {
    /// get the unary operation for left side unary operation
    ///
    /// eg:
    /// `-a` `!a` `&a`
    pub fn left_from_token(tt: &TokenType) -> Option<UnOp> {
        match tt {
            TokenType::Minus => Some(UnOp::Negation),
            TokenType::Bang => Some(UnOp::Not),
            _ => None,
        }
    }

    /// get the unary operation for right side unary operation
    ///
    /// eg:
    /// `a.*`
    pub fn right_from_token(tt: &TokenType) -> Option<UnOp> {
        match tt {
            TokenType::DotStar => Some(UnOp::Dereference),
            _ => None,
        }
    }

    pub fn is_right(&self) -> bool {
        matches!(self, UnOp::Dereference)
    }

    pub fn is_left(&self) -> bool {
        !self.is_right()
    }
}

impl<E> PrettyDump<E> for UnOp {
    fn try_dump(&self, ctx: &mut PrettyCtxt, _: &E) -> io::Result<()> {
        write!(ctx.out, "{self:?}")
    }
}

/// An ast node with a span.
#[derive(Debug, Clone, PartialEq, Eq, Default, Hash)]
pub struct Spanned<T> {
    pub node: T,
    pub loc: Span,
}

impl<T: PrettyDump<E>, E> PrettyDump<E> for Spanned<T> {
    fn try_dump(&self, ctx: &mut PrettyCtxt, extra: &E) -> io::Result<()> {
        self.node.try_dump(ctx, extra)?;
        ctx.print_loc(&self.loc)?;

        Ok(())
    }
}

/// Mutability of something.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub enum Mutability {
    Not,
    Mut,
}

impl Mutability {
    /// Returns `""` or `"mut "` based on the mutability.
    pub fn prefix_str(self) -> &'static str {
        match self {
            Self::Not => "",
            Self::Mut => "mut ",
        }
    }

    /// Returns `"immutable"` or `"mutable"` based on the mutability.
    pub fn adjective_str(self) -> &'static str {
        match self {
            Self::Not => "immutable",
            Self::Mut => "mutable",
        }
    }

    /// Inverts the mutability
    pub fn invert(self) -> Mutability {
        match self {
            Self::Not => Self::Mut,
            Self::Mut => Self::Not,
        }
    }

    /// Returns true if `Mut`
    pub fn is_mut(self) -> bool {
        matches!(self, Self::Mut)
    }

    /// Returns true if `Not`
    pub fn is_not(self) -> bool {
        matches!(self, Self::Not)
    }
}

impl<E> PrettyDump<E> for Mutability {
    fn try_dump(&self, ctx: &mut PrettyCtxt, _: &E) -> io::Result<()> {
        match self {
            Self::Not => write!(ctx.out, "not"),
            Self::Mut => write!(ctx.out, "mut"),
        }
    }
}

/// Compile-time.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Comptime {
    Yes,
    No,
}

impl Comptime {
    /// Return `"comptime "` or `""` based on comptime-ness.
    pub fn prefix_str(self) -> &'static str {
        match self {
            Comptime::Yes => "comptime ",
            Comptime::No => "",
        }
    }
}

mod private {
    pub trait Sealed {}

    impl Sealed for super::CtYes {}
    impl Sealed for super::CtNo {}
}

/// [`Comptime`] equivalent but as a type so it can be used in generics params
pub trait CompileTime: private::Sealed {}

/// Yes. It **is** compile-time.
///
/// See [`CompileTime`] documentation
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct CtYes;
impl CompileTime for CtYes {}

/// No. It **is not** compile-time.
///
/// See [`CompileTime`] documentation
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct CtNo;
impl CompileTime for CtNo {}

/// ABI names usable in an extern block
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq, Hash)]
pub enum Abi {
    /// `C`
    #[default]
    C,
}

impl Abi {
    /// Abi name as an anonymous enum variant, like `.Field`.
    pub fn enum_str(&self) -> &'static str {
        match self {
            Abi::C => ".C",
        }
    }
}

impl FromStr for Abi {
    type Err = ();

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s {
            "C" => Ok(Abi::C),
            _ => Err(()),
        }
    }
}

impl<E> PrettyDump<E> for Abi {
    fn try_dump(&self, ctx: &mut PrettyCtxt, _: &E) -> io::Result<()> {
        match self {
            Abi::C => write!(ctx.out, "C"),
        }
    }
}

/// The thing that contains the items
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ItemContainer {
    Module,
    ExternBlock,
}

/// Kind of Item
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ItemKind {
    Fundef,
    Fundecl,
    GlobalDef,
    GlobalUninit,
    Module,
    ExternBlock,
    Directive,
}
