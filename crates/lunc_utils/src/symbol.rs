//! Symbol in the DSIR or the SCIR

use std::{
    fmt::{self, Display},
    io,
};

use crate::{
    Span, idtype,
    pretty::{PrettyCtxt, PrettyDump},
};

/// The underlying type of an expression
#[derive(Debug, Clone, PartialEq, Eq, Hash, Default)]
pub enum Type {
    /// The type is not yet evaluated, we don't know it yet, it's an error if an
    /// expression, after type checking, still has Unknown type
    #[default]
    Unknown,
    /// 8 bit signed integer
    I8,
    /// 16 bit signed integer
    I16,
    /// 32 bit signed integer
    I32,
    /// 64 bit signed integer
    I64,
    /// 128 bit signed integer
    I128,
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
    /// 128 bit unsigned integer
    U128,
    /// Pointer-sized bit unsigned integer
    Usz,
    /// Half precision floating point, IEEE 754
    F16,
    /// Single precision floating point, IEEE 754
    F32,
    /// Double precision floating point, IEEE 754
    F64,
    /// Quadruple precision floating point, IEEE 754
    F128,
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
    /// String slice, not yet implemented.
    Str,
    /// Unicode code point, AKA character
    Char,
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

impl Type {
    /// Can this type store an integer literal value?
    pub fn is_int(&self) -> bool {
        matches!(
            self,
            Type::I8
                | Type::I16
                | Type::I32
                | Type::I64
                | Type::I128
                | Type::Isz
                | Type::U8
                | Type::U16
                | Type::U32
                | Type::U64
                | Type::U128
                | Type::Usz
        )
    }

    /// Can this type store a float literal value?
    pub fn is_float(&self) -> bool {
        matches!(self, Type::F16 | Type::F32 | Type::F64 | Type::F128)
    }

    /// Returns the signedness of an integer type or `None` if it's not an
    /// integer
    pub fn signedness(&self) -> Option<Signedness> {
        match self {
            Type::I8 => Some(Signedness::Signed),
            Type::I16 => Some(Signedness::Signed),
            Type::I32 => Some(Signedness::Signed),
            Type::I64 => Some(Signedness::Signed),
            Type::I128 => Some(Signedness::Signed),
            Type::Isz => Some(Signedness::Signed),

            Type::U8 => Some(Signedness::Unsigned),
            Type::U16 => Some(Signedness::Unsigned),
            Type::U32 => Some(Signedness::Unsigned),
            Type::U64 => Some(Signedness::Unsigned),
            Type::U128 => Some(Signedness::Unsigned),
            Type::Usz => Some(Signedness::Unsigned),
            _ => None,
        }
    }

    /// If this type is [`Type::Unknown`] returns [`None`], if it is something
    /// else it returns [`Some(..)`] with the guarantee to not be
    /// [`Type::Unknown`]
    pub fn as_option(self) -> Option<Type> {
        match self {
            Type::Unknown => None,
            _ => Some(self),
        }
    }
}

impl PrettyDump for Type {
    fn try_dump(&self, ctx: &mut PrettyCtxt) -> io::Result<()> {
        write!(ctx.out, "{self}")
    }
}

impl Display for Type {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Type::Unknown => write!(f, "unknown"),
            Type::I8 => write!(f, "i8"),
            Type::I16 => write!(f, "i16"),
            Type::I32 => write!(f, "i32"),
            Type::I64 => write!(f, "i64"),
            Type::I128 => write!(f, "i128"),
            Type::Isz => write!(f, "isz"),
            Type::U8 => write!(f, "u8"),
            Type::U16 => write!(f, "u16"),
            Type::U32 => write!(f, "u32"),
            Type::U64 => write!(f, "u64"),
            Type::U128 => write!(f, "u128"),
            Type::Usz => write!(f, "usz"),
            Type::F16 => write!(f, "f16"),
            Type::F32 => write!(f, "f32"),
            Type::F64 => write!(f, "f64"),
            Type::F128 => write!(f, "f128"),
            Type::Bool => write!(f, "bool"),
            Type::Void => write!(f, "void"),
            Type::FunPtr { args, ret } => {
                write!(f, "*fun (")?;

                if let Some(arg) = args.first() {
                    arg.fmt(f)?;
                }

                if args.len() >= 2 {
                    for arg in &args[1..] {
                        write!(f, ", ")?;
                        arg.fmt(f)?;
                    }
                }

                write!(f, ") -> ")?;

                ret.fmt(f)?;

                Ok(())
            }
            Type::Ptr { mutable, typ } => {
                write!(f, "*")?;

                if *mutable {
                    write!(f, "mut")?;
                }

                write!(f, " ")?;

                typ.fmt(f)
            }
            Type::Noreturn => write!(f, "noreturn"),
            Type::Str => write!(f, "str"),
            Type::Char => write!(f, "char"),
            Type::Type => write!(f, "type"),
        }
    }
}

/// Signedness of an Integer [`Type`].
#[derive(Debug, Clone)]
pub enum Signedness {
    /// The integer type can only represent positive values
    Unsigned,
    /// The integer type can represent positive and negative values
    ///
    /// # Note
    ///
    /// A signed integer type, uses Two's complement
    Signed,
}

/// A maybe not yet evaluated Symbol
#[derive(Debug, Clone)]
pub enum LazySymbol {
    Name(String),
    Sym(Symbol),
}

impl LazySymbol {
    /// Unwraps the lazy symbol to a symbol
    ///
    /// # Panic
    ///
    /// This functions panics if it is called on a [`LazySymbol::Name(..)`]
    /// variant.
    pub fn unwrap_sym(&self) -> Symbol {
        self.symbol()
            .expect("called 'unwrap_sym' on a Name variant")
    }

    /// Converts this lazy symbol to an option of a symbol.
    pub fn symbol(&self) -> Option<Symbol> {
        match self {
            Self::Name(_) => None,
            Self::Sym(sym) => Some(sym.clone()),
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

impl From<Symbol> for LazySymbol {
    fn from(value: Symbol) -> Self {
        LazySymbol::Sym(value)
    }
}

// /// A reference to a symbol, used to mutate symbols during resolution,
// /// everywhere both in SymbolTable and in the DSIR
// ///
// /// # Note
// ///
// /// This type is a wrapper of Arc so a clone of this type is very cheap.
// #[repr(transparent)]
// #[derive(Debug)]
// pub struct Symbol(Arc<RwLock<InternalSymbol__>>);

idtype! {
    /// A symbol
    pub struct Symbol [ Clone, PartialEq ] {
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
        /// ### Note
        ///
        /// This field is always [`Type::Unknown`] during desugaring, only in
        /// semantic checking this will be populated, the only exception is
        /// primitive types that havge type [`Type::Type`].
        pub typ: Type,
        /// the value of a global symbol
        ///
        /// ### Type
        ///
        /// A primitive type always have a value `ValueExpr::Type(...)`
        /// where for example the type expression `usz` will have a value of
        /// `ValueExpr::Type(Type::Usz)`, etc..
        ///
        /// ### Comptime evaluation of Symbol
        ///
        /// When we desugar the ast no symbols (expected from primitive types) have
        /// a value. The value is evaluated if we know its expression at compile
        /// time, then this field will be populated with a value.
        ///
        /// ### Global Defs
        ///
        /// A global definition (that is not a function) gets its value evaluated
        /// after the pre checking. The value of a symbol for a global symbol that
        /// is mutable is it's initial one.
        pub value: Option<ValueExpr>,
        /// location of the identifier defining this symbol
        pub loc: Option<Span>,
    }

    impl clone_methods for Symbol;

    impl PartialEq for Symbol;
}

impl Symbol {
    /// Create a new symbol with an unknown type.
    pub fn with(
        kind: SymKind,
        name: String,
        which: usize,
        path: EffectivePath,
        loc: Option<Span>,
    ) -> Symbol {
        Symbol::new(InternalSymbol {
            kind,
            name,
            which,
            path,
            typ: Type::Unknown,
            value: None,
            loc,
        })
    }

    /// Create a new symbol with kind local and no type.
    pub fn local(mutable: bool, name: String, which: usize, loc: Option<Span>) -> Symbol {
        Symbol::with(
            SymKind::Local { mutable },
            name.clone(),
            which,
            EffectivePath::with_root_member(name),
            loc,
        )
    }

    /// Create a new symbol with kind argument and no type.
    pub fn arg(name: String, which: usize, loc: Option<Span>) -> Symbol {
        Symbol::with(
            SymKind::Arg,
            name.clone(),
            which,
            EffectivePath::with_root_member(name),
            loc,
        )
    }

    /// Create a new symbol with kind global and no type.
    pub fn global(mutable: bool, name: String, path: EffectivePath, loc: Option<Span>) -> Symbol {
        Symbol::with(SymKind::Global { mutable }, name, 0, path, loc)
    }

    /// Create a new type, global, only used in `first_scope` on SymbolMap in
    /// DSIR
    ///
    /// # Note
    ///
    /// This is an exception, we assign a type and a compile time value to those
    /// global types, now because later will be painful
    pub fn new_typ(name: &str, typ: Type) -> Symbol {
        Symbol::new(InternalSymbol {
            kind: SymKind::Global { mutable: false },
            name: name.to_string(),
            which: 0,
            path: EffectivePath::new(),
            typ: Type::Type,
            value: Some(ValueExpr::Type(typ)),
            loc: None,
        })
    }

    /// Create a new symbol with kind function and no type.
    pub fn function(name: String, path: EffectivePath, loc: Option<Span>) -> Symbol {
        Symbol::with(SymKind::Function, name, 0, path, loc)
    }

    /// Create a new symbol with kind module and no type.
    pub fn module(name: String, path: EffectivePath, loc: Option<Span>) -> Symbol {
        Symbol::with(SymKind::Module, name, 0, path, loc)
    }

    /// See documentation of `is_place` on `ScExpression`
    pub fn is_place(&self) -> bool {
        self.inspect(|sym| {
            matches!(
                sym.kind,
                SymKind::Local { mutable: true } | SymKind::Global { mutable: true }
            )
        })
    }

    /// Returns true if the symbol is known at compile time, like immutable
    /// local variables or immutable global variables or functions
    pub fn is_comptime_known(&self) -> bool {
        self.inspect(|sym| {
            matches!(
                sym.kind,
                SymKind::Local { mutable: false }
                    | SymKind::Global { mutable: false }
                    | SymKind::Function
            )
        })
    }

    /// Get the kind of the symbol
    pub fn kind(&self) -> SymKind {
        let db = Self::database().lock();

        db.get(self.0).read().unwrap().kind.clone()
    }

    /// Get the location of the symbol
    pub fn loc(&self) -> Option<Span> {
        let db = Self::database().lock();

        db.get(self.0).read().unwrap().loc.clone()
    }

    /// Get the value of the symbol
    pub fn value(&self) -> Option<ValueExpr> {
        let db = Self::database().lock();

        db.get(self.0).read().unwrap().value.clone()
    }

    /// Get the typ of the symbol
    pub fn typ(&self) -> Type {
        let db = Self::database().lock();

        db.get(self.0).read().unwrap().typ.clone()
    }

    /// Get the path of the symbol
    pub fn path(&self) -> EffectivePath {
        let db = Self::database().lock();

        db.get(self.0).read().unwrap().path.clone()
    }
}

impl PrettyDump for Symbol {
    fn try_dump(&self, ctx: &mut PrettyCtxt) -> io::Result<()> {
        self.inspect(|sym| {
            let InternalSymbol {
                kind,
                name,
                which,
                path,
                typ,
                value,
                loc,
            } = &sym;

            ctx.pretty_struct("Symbol")
                .field("kind", kind)
                .field("name", (name, loc))
                .field("which", which)
                .field("path", path)
                .field("typ", typ)
                .field("value", value)
                .finish()?;

            Ok(())
        })
    }
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

    /// Returns a reference to the first member of the effective path
    pub fn first(&self) -> Option<&String> {
        self.0.first()
    }

    /// Push a new member to the path
    pub fn push(&mut self, member: String) {
        self.0.push(member)
    }

    /// Pops the last member of the path and returns it
    pub fn pop(&mut self) -> Option<String> {
        self.0.pop()
    }

    /// Is this path, a path to root? `orb` -> true, something else false.
    pub fn is_root(&self) -> bool {
        self.0 == ["orb"]
    }

    /// Append a path to this path
    pub fn append(&mut self, mut other: EffectivePath) {
        self.0.append(&mut other.0);
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

/// A value of an expression evaluated at compile time, during constant folding of SCIR or types are also ValueExprs.
#[derive(Debug, Clone, PartialEq)]
pub enum ValueExpr {
    /// Internal value of a type
    Type(Type),
    Boolean(bool),
    I8(i8),
    I16(i16),
    I32(i32),
    I64(i64),
    I128(i128),
    Isz(isize),
    U8(u8),
    U16(u16),
    U32(u32),
    U64(u64),
    U128(u128),
    Usz(usize),
    Str(String),
    Char(char),
    F32(f32),
    F64(f64),
}

impl ValueExpr {
    pub fn as_type(self) -> Option<Type> {
        match self {
            ValueExpr::Type(typ) => Some(typ),
            _ => None,
        }
    }
}

impl PrettyDump for ValueExpr {
    fn try_dump(&self, ctx: &mut PrettyCtxt) -> io::Result<()> {
        match self {
            ValueExpr::Type(typ) => {
                ctx.pretty_struct("Type").field("type", typ).finish()?;

                Ok(())
            }
            ValueExpr::Boolean(b) => {
                ctx.pretty_struct("Boolean").field("val", b).finish()?;

                Ok(())
            }
            ValueExpr::I8(i) => {
                ctx.pretty_struct("I8").field("val", i).finish()?;

                Ok(())
            }
            ValueExpr::I16(i) => {
                ctx.pretty_struct("I16").field("val", i).finish()?;

                Ok(())
            }
            ValueExpr::I32(i) => {
                ctx.pretty_struct("I32").field("val", i).finish()?;

                Ok(())
            }
            ValueExpr::I64(i) => {
                ctx.pretty_struct("I64").field("val", i).finish()?;

                Ok(())
            }
            ValueExpr::I128(i) => {
                ctx.pretty_struct("I128").field("val", i).finish()?;

                Ok(())
            }
            ValueExpr::Isz(i) => {
                ctx.pretty_struct("Isz").field("val", i).finish()?;

                Ok(())
            }
            ValueExpr::U8(i) => {
                ctx.pretty_struct("U8").field("val", i).finish()?;

                Ok(())
            }
            ValueExpr::U16(i) => {
                ctx.pretty_struct("U16").field("val", i).finish()?;

                Ok(())
            }
            ValueExpr::U32(i) => {
                ctx.pretty_struct("U32").field("val", i).finish()?;

                Ok(())
            }
            ValueExpr::U64(i) => {
                ctx.pretty_struct("U64").field("val", i).finish()?;

                Ok(())
            }
            ValueExpr::U128(i) => {
                ctx.pretty_struct("U128").field("val", i).finish()?;

                Ok(())
            }
            ValueExpr::Usz(i) => {
                ctx.pretty_struct("Usz").field("val", i).finish()?;

                Ok(())
            }
            ValueExpr::Str(str) => {
                ctx.pretty_struct("Str").field("val", str).finish()?;

                Ok(())
            }
            ValueExpr::Char(c) => {
                ctx.pretty_struct("Char").field("val", c).finish()?;

                Ok(())
            }
            ValueExpr::F32(f) => {
                ctx.pretty_struct("F32").field("val", f).finish()?;

                Ok(())
            }
            ValueExpr::F64(f) => {
                ctx.pretty_struct("F64").field("val", f).finish()?;

                Ok(())
            }
        }
    }
}
