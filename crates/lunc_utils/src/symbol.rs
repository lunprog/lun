//! Symbol in the DSIR or the SCIR

use std::{
    fmt::Display,
    io,
    ops::Deref,
    sync::{Arc, RwLock},
};

use crate::{
    Span,
    pretty::{PrettyCtxt, PrettyDump},
};

/// The underlying type of an expression
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Type {
    /// 8 bit signed integer
    I8,
    /// 16 bit signed integer
    I16,
    /// 32 bit signed integer
    I32,
    /// 64 bit signed integer
    I64,
    /// Pointer-sized bit signed integer
    Isz,
    /// 8 bit unsigned integer
    U8,
    /// 16 bit unsigned integer
    U16,
    /// 32 bit unsigned integer
    U32,
    /// 64 bit unsigned integer
    U64,
    /// Pointer-sized bit unsigned integer
    Usz,
    /// Single precision floating point, IEEE 754
    F32,
    /// Double precision floating point, IEEE 754
    F64,
    /// Boolean,
    ///
    /// only to legal values, `0 -> false` and `1 -> true`
    Bool,
    /// Void, nothing returned, this type is a `Zero Sized Type`.
    Void,
    /// Function Pointer
    FunPtr { args: Vec<Type>, ret: Box<Type> },
    /// Pointer
    Ptr { mutable: bool, typ: Box<Type> },
    /// Noreturn, this type indicates that the expression when evaluated stops
    /// the control flow, it is the type of a `break`, `continue` or `return`
    /// expression.
    Noreturn,
    /// Type, it is the "type" of a type, because types in Lun are first class
    /// citizens.
    ///
    /// eg:
    ///
    /// ```lun
    /// add :: fun(a: isz, b: isz) {
    ///     //        ^^^     ^^^ Here "isz" is an expression but it refers to
    ///     //                    the primitive type "isz" so the type of the
    ///     //                    expression "isz" is "type"
    /// }
    /// ```
    Type,
}

impl PrettyDump for Type {
    fn try_dump(&self, ctx: &mut PrettyCtxt) -> io::Result<()> {
        let out = &mut ctx.out;
        match self {
            Type::I8 => write!(out, "i8"),
            Type::I16 => write!(out, "i16"),
            Type::I32 => write!(out, "i32"),
            Type::I64 => write!(out, "i64"),
            Type::Isz => write!(out, "isz"),
            Type::U8 => write!(out, "u8"),
            Type::U16 => write!(out, "u16"),
            Type::U32 => write!(out, "u32"),
            Type::U64 => write!(out, "u64"),
            Type::Usz => write!(out, "usz"),
            Type::F32 => write!(out, "f32"),
            Type::F64 => write!(out, "f64"),
            Type::Bool => write!(out, "bool"),
            Type::Void => write!(out, "void"),
            Type::FunPtr { args, ret } => {
                write!(ctx.out, "*fun (")?;

                if let Some(arg) = args.first() {
                    arg.try_dump(ctx)?;
                }

                for arg in &args[1..] {
                    write!(ctx.out, ", ")?;
                    arg.try_dump(ctx)?;
                }

                write!(ctx.out, ") -> ")?;

                ret.try_dump(ctx)?;

                Ok(())
            }
            Type::Ptr { mutable, typ } => {
                write!(out, "*")?;

                if *mutable {
                    write!(out, "mut")?;
                }

                write!(out, " ")?;

                typ.try_dump(ctx)
            }
            Type::Noreturn => write!(out, "noreturn"),
            Type::Type => write!(out, "type"),
        }
    }
}

/// A maybe not yet evaluated Symbol
#[derive(Debug, Clone)]
pub enum LazySymbol {
    Name(String),
    Sym(SymbolRef),
}

impl LazySymbol {
    pub fn as_sym(&self) -> SymbolRef {
        match self {
            Self::Name(_) => panic!("called 'as_sym' on a Name variant"),
            Self::Sym(symref) => symref.clone(),
        }
    }
}

impl PrettyDump for LazySymbol {
    fn try_dump(&self, ctx: &mut PrettyCtxt) -> io::Result<()> {
        match self {
            LazySymbol::Name(id) => write!(ctx.out, "lazy {id}"),
            LazySymbol::Sym(sym) => sym.try_dump(ctx),
        }
    }
}

impl From<String> for LazySymbol {
    fn from(value: String) -> Self {
        LazySymbol::Name(value)
    }
}

impl From<SymbolRef> for LazySymbol {
    fn from(value: SymbolRef) -> Self {
        LazySymbol::Sym(value)
    }
}

/// A reference to a symbol, used to mutate symbols during resolution,
/// everywhere both in SymbolTable and in the DSIR
///
/// # Note
///
/// This type is a wrapper of Arc so a clone of this type is very cheap.
#[repr(transparent)]
#[derive(Debug, Clone)]
pub struct SymbolRef(Arc<RwLock<Symbol>>);

impl SymbolRef {
    /// Create a new symbol without a type.
    pub fn new(
        kind: SymKind,
        name: String,
        which: usize,
        path: EffectivePath,
        loc: Option<Span>,
    ) -> SymbolRef {
        SymbolRef(Arc::new(RwLock::new(Symbol {
            kind,
            name,
            which,
            path,
            typ: None,
            loc,
        })))
    }

    /// Create a new symbol with kind local and no type.
    pub fn local(mutable: bool, name: String, which: usize, loc: Option<Span>) -> SymbolRef {
        SymbolRef::new(
            SymKind::Local { mutable },
            name.clone(),
            which,
            EffectivePath::with_root_member(name),
            loc,
        )
    }

    /// Create a new symbol with kind argument and no type.
    pub fn arg(name: String, which: usize, loc: Option<Span>) -> SymbolRef {
        SymbolRef::new(
            SymKind::Arg,
            name.clone(),
            which,
            EffectivePath::with_root_member(name),
            loc,
        )
    }

    /// Create a new symbol with kind global and no type.
    pub fn global(
        mutable: bool,
        name: String,
        path: EffectivePath,
        loc: Option<Span>,
    ) -> SymbolRef {
        SymbolRef::new(SymKind::Global { mutable }, name, 0, path, loc)
    }

    /// Create a new symbol with kind function and no type.
    pub fn function(name: String, path: EffectivePath, loc: Option<Span>) -> SymbolRef {
        SymbolRef::new(SymKind::Function, name, 0, path, loc)
    }

    /// Create a new symbol with kind module and no type.
    pub fn module(name: String, path: EffectivePath, loc: Option<Span>) -> SymbolRef {
        SymbolRef::new(SymKind::Module, name, 0, path, loc)
    }
}

impl Deref for SymbolRef {
    type Target = Arc<RwLock<Symbol>>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl PrettyDump for SymbolRef {
    fn try_dump(&self, ctx: &mut PrettyCtxt) -> io::Result<()> {
        let Symbol {
            kind,
            name,
            which,
            path,
            typ,
            loc,
        } = &*self.read().unwrap();

        ctx.pretty_struct("Symbol")
            .field("kind", kind)
            .field("name", (name, loc))
            .field("which", which)
            .field("path", path)
            .field("typ", typ)
            .finish()?;

        Ok(())
    }
}

/// A symbol
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Symbol {
    /// kind of symbol
    pub kind: SymKind,
    /// name when defined, it's not the full path
    pub name: String,
    /// (can't be explained easily)
    ///
    /// eg:
    /// - for a function the `which` of the first argument is 0, the second is 1
    /// - for a variable the `which` is set to 0 for the first variable, 1 for the
    ///   second etc..
    /// - for a global and a function this field is not really relevant, but is
    ///   still populated
    pub which: usize,
    /// the absolute path to the symbol
    pub path: EffectivePath,
    /// the type of the symbol
    ///
    /// # Note
    ///
    /// This field is always `None` during desugaring, only in semantic checking
    /// this will be populated
    pub typ: Option<Type>,
    /// location of the identifier defining this symbol
    pub loc: Option<Span>,
}

/// The kind of symbol
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum SymKind {
    /// Local variable
    Local { mutable: bool },
    /// Argument
    Arg,
    /// Global
    Global { mutable: bool },
    /// Function
    Function,
    /// Module
    Module,
}

impl SymKind {
    pub fn is_global_def(&self) -> bool {
        matches!(self, Self::Global { .. } | Self::Function | Self::Module)
    }
}

impl Display for SymKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            SymKind::Local { .. } => f.write_str("local"),
            SymKind::Arg => f.write_str("argument"),
            SymKind::Global { .. } => f.write_str("global"),
            SymKind::Function => f.write_str("function"),
            SymKind::Module => f.write_str("module"),
        }
    }
}

impl PrettyDump for SymKind {
    fn try_dump(&self, ctx: &mut PrettyCtxt) -> io::Result<()> {
        write!(ctx.out, "{self}")
    }
}

/// A path to a definition in DSIR / DSIR
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct EffectivePath(Vec<String>);

impl EffectivePath {
    /// Creates a new empty effective path
    pub const fn new() -> EffectivePath {
        EffectivePath(Vec::new())
    }

    /// Creates a new effective path with just a single member
    pub fn with_root_member(root_member: impl ToString) -> EffectivePath {
        EffectivePath(vec![root_member.to_string()])
    }

    /// Creates a new effective path from a vector
    pub fn from_vec(vec: Vec<String>) -> EffectivePath {
        assert!(!vec.is_empty());
        EffectivePath(vec)
    }

    /// Returns the amount of members in the path eg:
    ///
    /// `orb`             -> 1
    /// `orb.main`        -> 2
    /// `std.panic.Panic` -> 3
    /// etc..
    pub fn len(&self) -> usize {
        self.0.len()
    }

    /// Is the path empty?
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Returns a slice of the underlying path
    pub fn as_slice(&self) -> &[String] {
        &self.0
    }

    /// Returns a mutable reference to the last member of the effective path
    ///
    /// # Example
    ///
    /// `orb`        -> mut ref to `orb`
    /// `orb.driver` -> mut ref to `driver`
    /// *etc..*
    pub fn last_mut(&mut self) -> Option<&mut String> {
        self.0.last_mut()
    }

    /// Returns a reference to the last member of the effective path
    pub fn last(&self) -> Option<&String> {
        self.0.last()
    }

    /// Push a new member to the path
    pub fn push(&mut self, member: String) {
        self.0.push(member)
    }

    /// Pops the last member of the path and returns it
    pub fn pop(&mut self) -> Option<String> {
        self.0.pop()
    }

    pub fn is_root(&self) -> bool {
        self.0 == ["orb"]
    }
}

impl<S: ToString> FromIterator<S> for EffectivePath {
    /// Creates a new effective path from an iterator
    fn from_iter<T: IntoIterator<Item = S>>(iter: T) -> Self {
        EffectivePath(iter.into_iter().map(|m| m.to_string()).collect())
    }
}

impl Default for EffectivePath {
    fn default() -> Self {
        EffectivePath::new()
    }
}

impl Display for EffectivePath {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if !self.is_empty() {
            write!(f, "{}", self.as_slice().join("."))
        } else {
            write!(f, "∅")
        }
    }
}

impl PrettyDump for EffectivePath {
    fn try_dump(&self, ctx: &mut PrettyCtxt) -> io::Result<()> {
        write!(ctx.out, "{self}")
    }
}
