//! Symbol in the DSIR or the SCIR

use std::{
    fmt::{self, Display},
    io::{self, Write},
    ops::RangeInclusive,
};

use crate::{
    Span, idtype,
    pretty::{PrettyCtxt, PrettyDump},
    target::{PtrWidth, TargetTriplet},
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
    /// Minimum value of an `i8` Lun type.
    pub const MIN_I8: i128 = -128;

    /// Maximum value of an `i8` Lun type.
    pub const MAX_I8: i128 = 127;

    /// Minimum value of an `i16` Lun type.
    pub const MIN_I16: i128 = -32_768;

    /// Maximum value of an `i16` Lun type.
    pub const MAX_I16: i128 = 32_767;

    /// Minimum value of an `i32` Lun type.
    pub const MIN_I32: i128 = -2_147_483_648;

    /// Maximum value of an `i32` Lun type.
    pub const MAX_I32: i128 = 2_147_483_647;

    /// Minimum value of an `i64` Lun type.
    pub const MIN_I64: i128 = -9_223_372_036_854_775_808;

    /// Maximum value of an `i64` Lun type.
    pub const MAX_I64: i128 = 9_223_372_036_854_775_807;

    /// Minimum value of an `i128` Lun type.
    pub const MIN_I128: i128 = -170_141_183_460_469_231_731_687_303_715_884_105_728;

    /// Maximum value of an `i128` Lun type.
    pub const MAX_I128: i128 = 170_141_183_460_469_231_731_687_303_715_884_105_727;

    /// Minimum value of an `u8` Lun type.
    pub const MIN_U8: i128 = 0;

    /// Maximum value of an `u8` Lun type.
    pub const MAX_U8: i128 = 255;

    /// Minimum value of an `u16` Lun type.
    pub const MIN_U16: i128 = 0;

    /// Maximum value of an `u16` Lun type.
    pub const MAX_U16: i128 = 65_535;

    /// Minimum value of an `u32` Lun type.
    pub const MIN_U32: i128 = 0;

    /// Maximum value of an `u32` Lun type.
    pub const MAX_U32: i128 = 4_294_967_295;

    /// Minimum value of an `u64` Lun type.
    pub const MIN_U64: i128 = 0;

    /// Maximum value of an `u64` Lun type.
    pub const MAX_U64: i128 = 18_446_744_073_709_551_615;

    /// Minimum value of an `u128` Lun type.
    pub const MIN_U128: i128 = 0;

    /// Maximum value of an `u128` Lun type.
    pub const MAX_U128: u128 = 340_282_366_920_938_463_463_374_607_431_768_211_455;

    /// Minimum value of an `f16` Lun type.
    pub const MIN_F16: f64 = -65504.0;

    /// Maximum value of an `f16` Lun type.
    pub const MAX_F16: f64 = 65504.0;

    /// Minimum value of an `f32` Lun type.
    pub const MIN_F32: f64 = -3.402_823_47E+38;

    /// Maximum value of an `f32` Lun type.
    pub const MAX_F32: f64 = 3.402_823_47E+38;

    /// Minimum value of an `f64` Lun type.
    pub const MIN_F64: f64 = -1.797_693_134_862_315_7E+308;

    /// Maximum value of an `f64` Lun type.
    pub const MAX_F64: f64 = 1.797_693_134_862_315_7E+308;

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

    /// Is this type a mutable pointer type? `*mut T`?
    pub fn is_mut_ptr(&self) -> bool {
        matches!(
            self,
            Type::Ptr {
                mutable: true,
                typ: _
            }
        )
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

    /// Tries to convert a type to a function ptr, returns None if it is not a function pointer
    pub fn as_fun_ptr(self) -> Option<(Vec<Type>, Type)> {
        match self {
            Type::FunPtr { args, ret } => Some((args, *ret)),
            _ => None,
        }
    }

    /// Can the type (self) can coerce to type (other) ?
    pub fn can_coerce(&self, other: &Type) -> bool {
        match self {
            Type::Unknown => panic!("cannot call this function with 'Unknown'."),
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
            | Type::Usz => other.is_int(),
            Type::F16 | Type::F32 | Type::F64 | Type::F128 => other.is_float(),
            Type::Bool => other.is_int(),
            Type::Void | Type::FunPtr { .. } => false,
            Type::Ptr { mutable, typ } => matches!(
                other,
                Type::Ptr {
                    mutable: other_mut,
                    typ: other_ty
                } if other_mut == mutable && typ.can_coerce(other_ty)
            ),
            // NOTE: noreturn can coerce to everything.
            Type::Noreturn => true,
            Type::Str | Type::Char | Type::Type => false,
        }
    }

    /// Returns the maximum integer this integer type can store, returns None if
    /// it is not an integer type
    ///
    /// # Note
    ///
    /// This function doesn't work to get the maximum value of a u128, because
    /// it cannot be represented as a i128
    pub const fn integer_max(&self, target: &TargetTriplet) -> Option<i128> {
        match self {
            Type::I8 => Some(Type::MAX_I8),
            Type::I16 => Some(Type::MAX_I16),
            Type::I32 => Some(Type::MAX_I32),
            Type::I64 => Some(Type::MAX_I64),
            Type::I128 => Some(Type::MAX_I128),
            Type::Isz => match target.ptr_width() {
                PtrWidth::Ptr16 => Some(Type::MAX_I16),
                PtrWidth::Ptr32 => Some(Type::MAX_I32),
                PtrWidth::Ptr64 => Some(Type::MAX_I64),
            },
            Type::U8 => Some(Type::MAX_U8),
            Type::U16 => Some(Type::MAX_U16),
            Type::U32 => Some(Type::MAX_U32),
            Type::U64 => Some(Type::MAX_U64),
            Type::Usz => match target.ptr_width() {
                PtrWidth::Ptr16 => Some(Type::MAX_U16),
                PtrWidth::Ptr32 => Some(Type::MAX_U32),
                PtrWidth::Ptr64 => Some(Type::MAX_U64),
            },
            _ => None,
        }
    }

    /// Returns the minimum integer this integer type can store, returns None if
    /// it is not an integer type
    pub const fn integer_min(&self, target: &TargetTriplet) -> Option<i128> {
        match self {
            Type::I8 => Some(Type::MIN_I8),
            Type::I16 => Some(Type::MIN_I16),
            Type::I32 => Some(Type::MIN_I32),
            Type::I64 => Some(Type::MIN_I64),
            Type::I128 => Some(Type::MIN_I128),
            Type::Isz => match target.ptr_width() {
                PtrWidth::Ptr16 => Some(Type::MIN_I16),
                PtrWidth::Ptr32 => Some(Type::MIN_I32),
                PtrWidth::Ptr64 => Some(Type::MIN_I64),
            },
            Type::U8 => Some(Type::MIN_U8),
            Type::U16 => Some(Type::MIN_U16),
            Type::U32 => Some(Type::MIN_U32),
            Type::U64 => Some(Type::MIN_U64),
            Type::U128 => Some(Type::MIN_U128),
            Type::Usz => match target.ptr_width() {
                PtrWidth::Ptr16 => Some(Type::MIN_U16),
                PtrWidth::Ptr32 => Some(Type::MIN_U32),
                PtrWidth::Ptr64 => Some(Type::MIN_U64),
            },
            _ => None,
        }
    }

    /// Return the range of integer this integer type supports, returns None if
    /// it is note an integer
    ///
    /// # Note `u128` type
    ///
    /// Because we can't represent the maximum value of a `u128` inside a `i128`
    /// this function does not work for `u128`.
    pub const fn integer_range(&self, target: &TargetTriplet) -> Option<RangeInclusive<i128>> {
        // NOTE: we are not using `?` operator here because it's not supported
        // in const evaluation
        let min = match self.integer_min(target) {
            Some(min) => min,
            None => return None,
        };

        let max = match self.integer_max(target) {
            Some(max) => max,
            None => return None,
        };

        Some(min..=max)
    }

    /// Returns the maximum float this float type can store, returns None if
    /// it is not a float type
    ///
    /// # Note `f128`
    ///
    /// This function doesn't support f128 because they are not yet stable in Rust.
    pub const fn float_max(&self) -> Option<f64> {
        match self {
            Type::F16 => Some(Type::MAX_F16),
            Type::F32 => Some(Type::MAX_F32),
            Type::F64 => Some(Type::MAX_F64),
            _ => None,
        }
    }

    /// Returns the minimum float this float type can store, returns None if
    /// it is not a float type
    ///
    /// # Note `f128`
    ///
    /// This function doesn't support f128 because they are not yet stable in Rust.
    pub const fn float_min(&self) -> Option<f64> {
        match self {
            Type::F16 => Some(Type::MIN_F16),
            Type::F32 => Some(Type::MIN_F32),
            Type::F64 => Some(Type::MIN_F64),
            _ => None,
        }
    }

    /// Return the range of float this float type supports, returns None if it
    /// is note an float
    ///
    /// # Note `f128`
    ///
    /// This function doesn't support f128 because they are not yet stable in Rust.
    pub const fn float_range(&self) -> Option<RangeInclusive<f64>> {
        // NOTE: we are not using `?` operator here because it's not supported
        // in const evaluation
        let min = match self.float_min() {
            Some(min) => min,
            None => return None,
        };

        let max = match self.float_max() {
            Some(max) => max,
            None => return None,
        };

        Some(min..=max)
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

idtype! {
    /// A symbol
    ///
    /// # Design decision
    ///
    /// Symbol is an idtype because in the dsir and the scir, we want to mutate
    /// every reference of a symbol and using idtype's is fast, memory efficient
    /// and easier than `Arc<RwLock<InternalSymbol>>` everywhere.
    pub struct Symbol [ Clone, PartialEq ] {
        /// kind of symbol
        pub kind: SymKind,
        /// name when defined, it's not the full path
        pub name: String,
        /// real, unmagled name of the symbol
        pub realname: Option<String>,
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
        /// the typeness of the `typ`.
        pub typeness: Typeness,
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

    impl FieldSet<typ: Type> for Symbol;

    impl FieldSet<value: Option<ValueExpr>> for Symbol;

    impl FieldGet<pub name: String> for Symbol;

    impl FieldGet<pub realname: Option<String>> for Symbol;

    impl FieldGet<pub kind: SymKind> for Symbol;

    impl FieldGet<pub loc: Option<Span>> for Symbol;

    impl FieldGet<pub value: Option<ValueExpr>> for Symbol;

    impl FieldGet<pub typ: Type> for Symbol;

    impl FieldGet<pub typeness: Typeness> for Symbol;

    impl FieldGet<pub path: EffectivePath> for Symbol;
}

impl Symbol {
    /// Create a new symbol with an unknown type.
    pub fn with(
        kind: SymKind,
        name: String,
        which: usize,
        path: EffectivePath,
        typeness: Typeness,
        loc: Option<Span>,
    ) -> Symbol {
        Symbol::with_internal(InternalSymbol {
            kind,
            name,
            realname: None,
            which,
            path,
            typ: Type::Unknown,
            typeness,
            value: None,
            loc,
        })
    }

    /// Create a new symbol with kind local and no type.
    pub fn local(
        mutable: bool,
        name: String,
        which: usize,
        typeness: Typeness,
        loc: Option<Span>,
    ) -> Symbol {
        Symbol::with(
            SymKind::Local { mutable },
            name.clone(),
            which,
            EffectivePath::with_root_member(name),
            typeness,
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
            Typeness::Explicit,
            loc,
        )
    }

    /// Create a new symbol with kind global and no type.
    pub fn global(
        mutable: bool,
        name: String,
        path: EffectivePath,
        typeness: Typeness,
        loc: Option<Span>,
    ) -> Symbol {
        Symbol::with(SymKind::Global { mutable }, name, 0, path, typeness, loc)
    }

    /// Create a new type, global, only used in `first_scope` on SymbolMap in
    /// DSIR
    ///
    /// # Note
    ///
    /// This is an exception, we assign a type and a compile time value to those
    /// global types, now because later will be painful
    pub fn new_typ(name: &str, typ: Type) -> Symbol {
        Symbol::with_internal(InternalSymbol {
            kind: SymKind::Global { mutable: false },
            name: name.to_string(),
            realname: None,
            which: 0,
            path: EffectivePath::new(),
            typ: Type::Type,
            typeness: Typeness::Explicit,
            value: Some(ValueExpr::Type(typ)),
            loc: None,
        })
    }

    /// Create a new symbol with kind function and no type.
    pub fn function(name: String, path: EffectivePath, loc: Option<Span>) -> Symbol {
        Symbol::with(SymKind::Function, name, 0, path, Typeness::Explicit, loc)
    }

    /// Create a new symbol with kind module and no type.
    pub fn module(name: String, path: EffectivePath, loc: Option<Span>) -> Symbol {
        Symbol::with(SymKind::Module, name, 0, path, Typeness::Explicit, loc)
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

    // NOTE: this is probably fine for now but if we allow interior mutability,
    // it can lead to bugs.
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
}

impl PrettyDump for Symbol {
    fn try_dump(&self, ctx: &mut PrettyCtxt) -> io::Result<()> {
        self.inspect(|sym| {
            let InternalSymbol {
                kind,
                name,
                realname,
                which,
                path,
                typ,
                typeness,
                value,
                loc,
            } = &sym;

            ctx.pretty_struct("Symbol")
                .field("kind", kind)
                .field("name", (name, loc))
                .field("realname", realname)
                .field("which", which)
                .field("path", path)
                .field("typ", typ)
                .field("typeness", typeness)
                .field("value", value)
                .finish()?;

            Ok(())
        })
    }
}

/// How the type of the symbol has been computed
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Typeness {
    /// The type was inferred from an expression and can be coerced to another
    /// type.
    Implicit,
    /// The type was explicitly written in the source code, and tho the type
    /// cannot be coerced to another type.
    Explicit,
}

impl Display for Typeness {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Typeness::Implicit => write!(f, "implicit"),
            Typeness::Explicit => write!(f, "explicit"),
        }
    }
}

impl PrettyDump for Typeness {
    fn try_dump(&self, ctx: &mut PrettyCtxt) -> io::Result<()> {
        write!(ctx.out, "{self}")
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

    /// Can this kind of symbol allow shadowing?
    pub fn can_shadow(&self) -> bool {
        matches!(self, SymKind::Local { .. } | SymKind::Arg)
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

    /// Returns a mutable reference to the first member of the effective path
    pub fn first_mut(&mut self) -> Option<&mut String> {
        self.0.first_mut()
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

    /// Return a slice of the members
    pub fn members(&self) -> &[String] {
        &self.0
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

macro_rules! value_expr_impl_op {
    {name = $name:ident, errmsg = $errmsg:expr, int_fn = $int_fn:ident, float_fn = $float_fn:expr,} => {
        /// Tries to perform an operation on two value expression if supported
        /// returns the expected value, otherwise returns an error that maybe
        /// contains a note.
        ///
        /// # Note
        ///
        /// This operation only works if both values have the same type.
        pub fn $name(&self, other: &ValueExpr) -> Result<Self, Option<String>> {
            use ValueExpr::*;
            let err = Some($errmsg.to_string());

            match (self, other) {
                // signed integers
                (I8(lhs), I8(rhs)) => Ok(I8(lhs.$int_fn(*rhs).ok_or(err)?)),
                (I16(lhs), I16(rhs)) => Ok(I16(lhs.$int_fn(*rhs).ok_or(err)?)),
                (I32(lhs), I32(rhs)) => Ok(I32(lhs.$int_fn(*rhs).ok_or(err)?)),
                (I64(lhs), I64(rhs)) => Ok(I64(lhs.$int_fn(*rhs).ok_or(err)?)),
                (I128(lhs), I128(rhs)) => Ok(I128(lhs.$int_fn(*rhs).ok_or(err)?)),

                // unsigned integers
                (U8(lhs), U8(rhs)) => Ok(U8(lhs.$int_fn(*rhs).ok_or(err)?)),
                (U16(lhs), U16(rhs)) => Ok(U16(lhs.$int_fn(*rhs).ok_or(err)?)),
                (U32(lhs), U32(rhs)) => Ok(U32(lhs.$int_fn(*rhs).ok_or(err)?)),
                (U64(lhs), U64(rhs)) => Ok(U64(lhs.$int_fn(*rhs).ok_or(err)?)),
                (U128(lhs), U128(rhs)) => Ok(U128(lhs.$int_fn(*rhs).ok_or(err)?)),

                // floats
                (F32(lhs), F32(rhs)) => Ok(F32($float_fn(lhs, rhs))),
                (F64(lhs), F64(rhs)) => Ok(F64($float_fn(lhs, rhs))),
                _ => Err(None),
            }
        }
    };
}

/// A value of an expression evaluated at compile time, during constant folding
/// of SCIR or types are also ValueExprs.
///
/// # Note
///
/// There is no `Usz` or `Isz` value expr, it's because we replace it when we do
/// the evaluation to the corresponding integer.
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
    U8(u8),
    U16(u16),
    U32(u32),
    U64(u64),
    U128(u128),
    Str(String),
    Char(char),
    F32(f32),
    F64(f64),
    Void,
}

use std::ops::{Add, Div, Mul, Rem, Sub};

impl ValueExpr {
    /// Tries to convert this value to a type.
    pub fn as_type(self) -> Option<Type> {
        match self {
            ValueExpr::Type(typ) => Some(typ),
            _ => None,
        }
    }

    value_expr_impl_op! {
        name = add,
        errmsg = "integer overflow",
        int_fn = checked_add,
        float_fn = Add::add,
    }

    value_expr_impl_op! {
        name = sub,
        errmsg = "integer overflow",
        int_fn = checked_sub,
        float_fn = Sub::sub,
    }

    value_expr_impl_op! {
        name = mul,
        errmsg = "integer overflow",
        int_fn = checked_mul,
        float_fn = Mul::mul,
    }

    value_expr_impl_op! {
        name = div,
        errmsg = "integer overflow",
        int_fn = checked_div,
        float_fn = Div::div,
    }

    value_expr_impl_op! {
        name = rem,
        errmsg = "integer overflow",
        int_fn = checked_rem,
        float_fn = Rem::rem,
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
            ValueExpr::Void => {
                write!(ctx.out, "void")
            }
        }
    }
}
