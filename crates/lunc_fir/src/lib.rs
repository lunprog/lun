//! Final Intermediate Representation of Lun, the closest one to the final
//! assembly or machine code.
//!
//! # What is fir?
//!
//! FIR is an SSA based, intermiadiate representation without a phi function but
//! with block arguments that replaces them.

use std::{
    fmt::{self, Display},
    io,
    num::NonZeroU32,
    ops::Deref,
};

use lunc_utils::{
    idtype,
    pretty::{PrettyCtxt, PrettyDump},
};

pub mod builder;

/// A FIR unit
#[derive(Debug, Clone)]
pub struct FirUnit {
    globals: Vec<Glob>,
    fundecls: Vec<FunDecl>,
    fundefs: Vec<FunDef>,
}

impl FirUnit {
    /// Create a new IR unit
    pub fn new() -> FirUnit {
        FirUnit {
            globals: Vec::new(),
            fundecls: Vec::new(),
            fundefs: Vec::new(),
        }
    }

    /// Append a function definition to the unit
    pub fn append_fundef(&mut self, def: FunDef) -> FunDef {
        self.fundefs.push(def);

        self.fundefs.last().unwrap().clone()
    }

    /// Append a function declaration to the unit
    pub fn append_fundecl(&mut self, decl: FunDecl) -> FunDecl {
        self.fundecls.push(decl);

        self.fundecls.last().unwrap().clone()
    }

    /// Append a global variable to the unit
    pub fn append_glob(&mut self, glob: Glob) -> Glob {
        self.globals.push(glob);

        self.globals.last().unwrap().clone()
    }
}

impl PrettyDump for FirUnit {
    fn try_dump(&self, ctx: &mut PrettyCtxt) -> io::Result<()> {
        writeln!(ctx.out, "// ======== FIR UNIT ========")?;

        if !self.globals.is_empty() {
            writeln!(ctx.out, "\n// Global variables")?;
            for glob in &self.globals {
                println!();
                glob.try_dump(ctx)?;
            }
        }

        if !self.fundecls.is_empty() {
            writeln!(ctx.out, "\n// Function declarations")?;
            for decl in &self.fundecls {
                println!();
                decl.try_dump(ctx)?;
            }
        }

        if !self.fundefs.is_empty() {
            writeln!(ctx.out, "\n// Function definitions")?;
            for fun in &self.fundefs {
                println!();
                fun.try_dump(ctx)?;
            }
        }

        ctx.out.flush()?;

        Ok(())
    }
}

impl Default for FirUnit {
    fn default() -> Self {
        FirUnit::new()
    }
}

/// First class type, they can only be produced by instructions.
///
/// It is a subset of [`Type`].
///
/// [`Type`]: lunc_utils::symbol::Type
#[derive(Debug, Clone)]
pub enum FcType {
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
    /// Single precision floating point, IEEE 754
    F32,
    /// Double precision floating point, IEEE 754
    F64,
    /// Boolean,
    ///
    /// only to legal values, `0 -> false` and `1 -> true`
    Bool,
    /// Void, nothing returned, this type is a `ZST`.
    Void,
    /// Function Pointer
    FunPtr { args: Vec<FcType>, ret: Box<FcType> },
    /// Pointer
    Ptr { ty: Box<FcType> },
    /// A fixed size array.
    Array { n: u64, ty: Box<FcType> },
}

impl FcType {
    /// Create a new pointer type
    pub fn ptr(ty: FcType) -> FcType {
        FcType::Ptr { ty: Box::new(ty) }
    }
}

impl Display for FcType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            FcType::I8 => write!(f, "i8"),
            FcType::I16 => write!(f, "i16"),
            FcType::I32 => write!(f, "i32"),
            FcType::I64 => write!(f, "i64"),
            FcType::I128 => write!(f, "i128"),
            FcType::U8 => write!(f, "u8"),
            FcType::U16 => write!(f, "u16"),
            FcType::U32 => write!(f, "u32"),
            FcType::U64 => write!(f, "u64"),
            FcType::U128 => write!(f, "u128"),
            FcType::F32 => write!(f, "f32"),
            FcType::F64 => write!(f, "f64"),
            FcType::Bool => write!(f, "bool"),
            FcType::Void => write!(f, "void"),
            FcType::FunPtr { args, ret } => {
                write!(f, "funptr (")?;

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
            FcType::Ptr { ty } => {
                write!(f, "ptr ")?;
                ty.fmt(f)
            }
            FcType::Array { n, ty } => {
                ty.fmt(f)?;

                write!(f, " x {n}")
            }
        }
    }
}

/// Name of a definition, used have the convenient `$my_global_name` or
/// `$'something with whitespaces or non-ascii'`
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Name(String);

impl Name {
    /// Create a new [`Name`] from a [`String`].
    pub fn from_string(str: impl ToString) -> Name {
        Name(str.to_string())
    }
}

impl Display for Name {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.0.is_ascii() && !self.0.contains(char::is_whitespace) {
            write!(f, "${}", self.0)
        } else {
            write!(f, "$'{}'", self.0)
        }
    }
}

impl Deref for Name {
    type Target = String;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

idtype! {
    /// Function declaration
    pub struct FunDecl {
        /// un mangled name of the function
        name: Name,
        /// arguments types
        args: Vec<FcType>,
        /// return type
        ret: FcType,
    }

    /// Function definition
    ///
    /// # Block entry
    ///
    /// The entry block of a function is the block where the function goes to when
    /// it is called. The entry block must:
    /// - have label `.bb0`
    /// - be the first block of the list of blocks
    /// - be present.
    ///
    /// The entry block gets as block argument the arguments of the function, a
    /// function is malformed if the entry block does not have exactly the same
    /// arguments as the function arguments.
    ///
    /// # Arguments
    ///
    /// Arguments, if any, can be accessed by using registers `%1` to `%N` where
    /// `N` is the arity of the function. Eg: a function with two arguments have
    /// the following registers allocated: `%1` for the first one and `%2` for the
    /// second one.
    ///
    /// eg:
    /// ```text
    /// define $'main'(%1: i32, %2: ptr ptr i8) -> i32 {
    ///     // ...
    /// }
    /// ```
    /// in this example we clearly see the registers next to the arguments
    pub struct FunDef {
        /// un mangled name of the function
        name: Name,
        /// arguments types
        args: Vec<FcType>,
        /// return type
        ret: FcType,
        /// basic blocks they compose the body of the function.
        bbs: Vec<BasicBlock>,
        /// is the signature of the function finished?
        sig_finished: bool,
    }

    impl FieldGet<sig_finished: bool> for FunDef;
}

impl FunDecl {
    /// Create a new function declaration with the arguments and the return type
    pub fn new(
        name: impl ToString,
        args: impl IntoIterator<Item = FcType>,
        ret: FcType,
    ) -> FunDecl {
        FunDecl::with_internal(InternalFunDecl {
            name: Name::from_string(name),
            args: args.into_iter().collect(),
            ret,
        })
    }
}

impl PrettyDump for FunDecl {
    fn try_dump(&self, ctx: &mut PrettyCtxt) -> io::Result<()> {
        self.inspect(|this| {
            let InternalFunDecl { name, args, ret } = this;

            write!(ctx.out, "declare {name}(")?;
            for (i, arg) in args.iter().enumerate() {
                write!(ctx.out, "{arg}")?;

                if i != args.len() - 1 {
                    write!(ctx.out, ", ")?;
                }
            }
            write!(ctx.out, ")")?;
            writeln!(ctx.out, " -> {ret};")?;

            Ok(())
        })
    }
}

impl FunDef {
    /// Create a new function with a name, no args and a default return type of
    /// `void`, and no basic blocks.
    pub fn new(name: impl ToString) -> FunDef {
        FunDef::with_args_ret_bbs(name.to_string(), Vec::new(), FcType::Void, Vec::new())
            .unfinished()
    }

    fn unfinished(self) -> FunDef {
        self.inspect_mut(|this| this.sig_finished = false);

        self
    }

    /// Create a new function definition with the arguments, the return type and
    /// the basic blocks.
    pub fn with_args_ret_bbs(
        name: String,
        args: Vec<FcType>,
        ret: FcType,
        bbs: Vec<BasicBlock>,
    ) -> FunDef {
        FunDef::with_internal(InternalFunDef {
            name: Name::from_string(name),
            args,
            ret,
            bbs,
            sig_finished: true,
        })
    }

    /// Append an argument to a function with an unfinished signature
    ///
    /// # Panic
    ///
    /// This method panics if the function signature is already finished.
    pub fn append_arg(&mut self, arg: FcType) {
        if self.sig_finished() {
            panic!("cannot mutate the signature of a function once it is finished.");
        }

        self.inspect_once(|this| this.args.push(arg));
    }

    /// Append some arguments to a function with an unfinished signature
    ///
    /// # Panic
    ///
    /// This method panics if the function signature is already finished.
    pub fn append_args(&mut self, arg: impl IntoIterator<Item = FcType>) {
        if self.sig_finished() {
            panic!("cannot mutate the signature of a function once it is finished.");
        }

        self.inspect_once(|this| {
            this.args.extend(arg);
        });
    }

    /// Set the return type of a function with an unfinished signature,
    /// overriding any previous return types.
    ///
    /// # Panic
    ///
    /// This method panics if the function signature is already finished.
    pub fn set_ret(&self, ret: FcType) {
        if self.sig_finished() {
            panic!("cannot mutate the signature of a function once it is finished.");
        }

        self.inspect_once(|this| this.ret = ret);
    }

    /// Mark the signature of the function as finished
    pub fn finish_sig(&mut self) {
        self.inspect_once(|this| this.sig_finished = true)
    }

    /// Get the basic block by label
    pub fn get_bb(&self, label: BbLabel) -> Option<BasicBlock> {
        self.inspect(|this| {
            this.bbs
                .iter()
                .find(|bb| bb.inspect(|bb| bb.label) == label)
                .cloned()
        })
    }

    /// Get the last basic block inserted
    pub fn last_bb(&self) -> Option<BasicBlock> {
        self.inspect(|this| this.bbs.last().cloned())
    }

    /// Get the entry basic block
    pub fn entry(&self) -> BasicBlock {
        self.inspect(|this| {
            let entry = this.bbs.first().unwrap().clone();

            assert!(entry.label() == BbLabel::new(0));

            entry
        })
    }
}

impl PrettyDump for FunDef {
    fn try_dump(&self, ctx: &mut PrettyCtxt) -> io::Result<()> {
        self.inspect(|this| {
            let InternalFunDef {
                name,
                args,
                ret,
                bbs,
                sig_finished: _,
            } = this;

            write!(ctx.out, "define {name}(")?;
            for (i, arg) in args.iter().enumerate() {
                write!(ctx.out, "{}: {arg}", Reg::new(i as u32 + 1))?;

                if i != args.len() - 1 {
                    write!(ctx.out, ", ")?;
                }
            }
            write!(ctx.out, ")")?;
            write!(ctx.out, " -> {ret} ")?;

            writeln!(ctx.out, "{{")?;

            for block in bbs {
                block.try_dump(ctx)?;
            }

            writeln!(ctx.out, "}}")?;

            Ok(())
        })
    }
}

idtype! {
    /// A global variable, can be read-only.
    pub struct Glob {
        /// name of the global variable, must be an unmangled name, used in linking,
        /// it's the name of the symbol
        name: Name,
        /// type of the global
        ty: FcType,
        /// read-only
        ro: bool,
        /// value
        val: ConstValue,
    }
}

impl Glob {
    /// Create a new global variable
    pub fn new(name: impl ToString, ty: FcType, ro: bool, val: ConstValue) -> Glob {
        Glob::with_internal(InternalGlob {
            name: Name::from_string(name),
            ty,
            ro,
            val,
        })
    }

    /// Create a new global variable with a string constant as its value
    pub fn string_const(name: impl ToString, string: impl AsRef<str>) -> Glob {
        let string = string.as_ref();

        Glob::new(
            name,
            FcType::Array {
                n: string.len() as u64,
                ty: Box::new(FcType::U8),
            },
            true,
            ConstValue::string(string),
        )
    }
}

impl PrettyDump for Glob {
    fn try_dump(&self, ctx: &mut PrettyCtxt) -> io::Result<()> {
        self.inspect(|this| {
            let out = &mut ctx.out;

            let InternalGlob {
                name,
                ty: typ,
                ro,
                val,
            } = this;

            write!(out, "{name}: {typ} ")?;

            if *ro {
                write!(out, "readonly")?;
            }

            writeln!(out, "= {val};")?;

            Ok(())
        })
    }
}

/// A constant value
#[derive(Debug, Clone)]
pub enum ConstValue {
    Bool(bool),
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
    F32(f32),
    F64(f64),
    /// # Note
    ///
    /// - the FIR, makes no guarantees about strings encoding, doesn't enforce
    ///   utf-8, but tries to print it as utf-8 when pretty printed, this exist
    ///   just to be able to pretty print it like a string.
    /// - **the only valid** place to have a string is in a [`Glob`], you cannot
    ///   have a string in where an [`Arg`] is expected in an [instruction].
    ///
    /// [instruction]: crate::Inst
    String(Box<[u8]>),
}

impl ConstValue {
    pub fn string(str: impl AsRef<[u8]>) -> ConstValue {
        ConstValue::String(Box::from(str.as_ref()))
    }
}

impl Display for ConstValue {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Bool(b) => write!(f, "{b}"),
            Self::I8(i) => write!(f, "{i}"),
            Self::I16(i) => write!(f, "{i}"),
            Self::I32(i) => write!(f, "{i}"),
            Self::I64(i) => write!(f, "{i}"),
            Self::I128(i) => write!(f, "{i}"),
            Self::U8(i) => write!(f, "{i}"),
            Self::U16(i) => write!(f, "{i}"),
            Self::U32(i) => write!(f, "{i}"),
            Self::U64(i) => write!(f, "{i}"),
            Self::U128(i) => write!(f, "{i}"),
            Self::String(str) => write!(f, "{:?}", String::from_utf8_lossy(str)),
            Self::F32(v) => write!(f, "{v:e}"),
            Self::F64(v) => write!(f, "{v:e}"),
        }
    }
}

/// A block label.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct BbLabel(u32);

impl BbLabel {
    /// Block label of the entry point of a function
    pub const ENTRY: BbLabel = BbLabel::new(0);

    /// Create a new block label
    pub const fn new(i: u32) -> BbLabel {
        BbLabel(i)
    }
}

impl Display for BbLabel {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, ".bb{}", self.0)
    }
}

idtype! {
    /// A basic block, is a list of instructions, that is finished by a terminating
    /// instruction.
    ///
    /// # Finished block guarantees
    ///
    /// - immutatability of the list of instructions and the terminal inst
    /// - the presence of a terminator instruction
    pub struct BasicBlock {
        /// label of the block
        label: BbLabel,
        /// arguments types
        args: Vec<FcType>,
        /// the instructions of the block
        insts: Vec<Inst>,
        /// terminator instruction of the block.
        terminator: Option<Terminator>,
        /// used to guarantee that the block is finished
        finished: bool,
    }

    impl FieldGet<finished: bool> for BasicBlock;

    impl FieldGet<pub label: BbLabel> for BasicBlock;
}

impl BasicBlock {
    /// Create a new basic block
    pub fn new(label: BbLabel, args: Vec<FcType>) -> BasicBlock {
        BasicBlock::with_internal(InternalBasicBlock {
            label,
            args,
            insts: Vec::new(),
            terminator: None,
            finished: false,
        })
    }

    /// Append an instruction
    pub fn append_inst(&mut self, inst: Inst) {
        assert!(
            !self.finished(),
            "cannot mutate block when it is already finished"
        );

        self.inspect_once(|this| {
            this.insts.push(inst);
        })
    }

    /// Set the terminal instruction
    pub fn set_terminator(&mut self, terminator: Terminator) {
        assert!(
            !self.finished(),
            "cannot mutate block when it is already finished"
        );

        self.inspect_once(|this| this.terminator = Some(terminator));
    }

    /// Finish the block
    ///
    /// # Panic
    ///
    /// This function panic if the block doesn't uphold the guarantees a
    /// finished block has.
    pub fn finish(&mut self) {
        self.inspect_mut(|this| {
            assert!(
                this.terminator.is_some(),
                "you must have a terminal instruction to make the block finished"
            );

            this.finished = true;
        });
    }

    /// Does the basic block has a terminator instruction set?
    pub fn is_terminated(&self) -> bool {
        self.inspect(|this| this.terminator.is_some())
    }
}

impl PrettyDump for BasicBlock {
    fn try_dump(&self, ctx: &mut PrettyCtxt) -> io::Result<()> {
        self.inspect(|this| {
            let InternalBasicBlock {
                label,
                args,
                insts,
                terminator,
                finished: _,
            } = this;

            if *label != BbLabel::ENTRY {
                write!(ctx.out, "{label} (")?;

                for (i, arg) in args.iter().enumerate() {
                    write!(ctx.out, "{}: {arg}", Reg::new(i as u32 + 1))?;

                    if i != args.len() - 1 {
                        write!(ctx.out, ", ")?;
                    }
                }

                writeln!(ctx.out, "):")?;
            }

            for inst in insts {
                writeln!(ctx.out, "    {inst}")?;
            }

            write!(ctx.out, "    ")?;
            terminator.try_dump(ctx)?;

            writeln!(ctx.out)?;

            Ok(())
        })
    }
}

/// An argument of an instruction
#[derive(Debug, Clone)]
pub enum Arg {
    /// A constant
    Constant(ConstValue),
    /// A register
    Reg(Reg),
    /// A reference to a global variable inside the current unit.
    Glob(Glob),
    /// A reference to a function definition or function declaration.
    Fun(Fun),
}

/// A function definition or declaration
#[derive(Debug, Clone)]
pub enum Fun {
    Def(FunDef),
    Decl(FunDecl),
}

impl From<FunDef> for Fun {
    fn from(def: FunDef) -> Self {
        Fun::Def(def)
    }
}

impl From<FunDecl> for Fun {
    fn from(decl: FunDecl) -> Self {
        Fun::Decl(decl)
    }
}

impl Arg {
    pub fn fun(fun: impl Into<Fun>) -> Arg {
        Arg::Fun(fun.into())
    }
}

impl Display for Arg {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Constant(constval) => write!(f, "{constval}"),
            Self::Glob(glob) => glob.inspect(|this| write!(f, "{}", this.name)),
            Self::Reg(reg) => write!(f, "{reg}"),
            Self::Fun(Fun::Def(def)) => def.inspect(|this| write!(f, "{}", this.name)),
            Self::Fun(Fun::Decl(decl)) => decl.inspect(|this| write!(f, "{}", this.name)),
        }
    }
}

/// Alignment of an allocation, especially a `salloc` allocation.
pub type Alignment = NonZeroU32;

/// An instruction of FIR.
#[derive(Debug, Clone)]
pub enum Inst {
    /// # Syntax
    ///
    /// `<res> = call <ty> <fnptr> ( <function args> )`
    ///
    /// # Description
    ///
    /// This instruction makes a call to the `<fnptr>`, with the args `<function
    /// args>`, puts the result of the call into `<res>`, the type of the
    /// returned value is specified with `<ty>`
    Call {
        res: Reg,
        ty: FcType,
        fnptr: Arg,
        args: Vec<Arg>,
    },
    /// # Syntax
    ///
    /// `<res> = add <ty>, <lhs>, <rhs>`
    ///
    /// # Description
    ///
    /// Performs an addition, `lhs + rhs` that must be of type `ty`, the result
    /// is then put in `<res>`. The type must be an integer type and works for
    /// both signed and unsigned integer types, `iNN` / `uNN`.
    ///
    /// ## Overflow
    ///
    /// If an overflow occurs, the result of the operation is a poisoned value.
    Add {
        res: Reg,
        ty: FcType,
        lhs: Arg,
        rhs: Arg,
    },
    /// # Syntax
    ///
    /// `<res> = fadd <ty>, <lhs>, <rhs>`
    ///
    /// # Description
    ///
    /// Performs a floating point addition, `lhs + rhs` that must be of type
    /// `ty`, the result is then put in `<res>`. The type must be a floating
    /// point type.
    Fadd {
        res: Reg,
        ty: FcType,
        lhs: Arg,
        rhs: Arg,
    },
    /// # Syntax
    ///
    /// `<res> = sub <ty>, <lhs>, <rhs>`
    ///
    /// # Description
    ///
    /// Performs a subtraction, `lhs - rhs` that must be of type `ty`, the
    /// result is then put in `<res>`. The type must be an integer type and
    /// works for both signed and unsigned integer types, `iNN` / `uNN`.
    ///
    /// ## Overflow
    ///
    /// If an overflow occurs, the result of the operation is a poisoned value.
    Sub {
        res: Reg,
        ty: FcType,
        lhs: Arg,
        rhs: Arg,
    },
    /// # Syntax
    ///
    /// `<res> = fsub <ty>, <lhs>, <rhs>`
    ///
    /// # Description
    ///
    /// Performs a floating point subtraction, `lhs - rhs` that must be of type
    /// `ty`, the result is then put in `<res>`. The type must be a floating
    /// point type.
    Fsub {
        res: Reg,
        ty: FcType,
        lhs: Arg,
        rhs: Arg,
    },
    /// # Syntax
    ///
    /// `<res> = mul <ty>, <lhs>, <rhs>`
    ///
    /// # Description
    ///
    /// Performs a multiplication, `lhs * rhs` that must be of type `ty`, the
    /// result is then put in `<res>`. The type must be an integer type and
    /// works for both signed and unsigned integer types, `iNN` / `uNN`.
    ///
    /// ## Overflow
    ///
    /// If an overflow occurs, the result of the operation is a poisoned value.
    Mul {
        res: Reg,
        ty: FcType,
        lhs: Arg,
        rhs: Arg,
    },
    /// # Syntax
    ///
    /// `<res> = fmul <ty>, <lhs>, <rhs>`
    ///
    /// # Description
    ///
    /// Performs a floating point multiplication, `lhs * rhs` that must be
    /// of type `ty`, the result is then put in `<res>`. The type must be a
    /// floating point type.
    Fmul {
        res: Reg,
        ty: FcType,
        lhs: Arg,
        rhs: Arg,
    },
    /// # Syntax
    ///
    /// `<res> = udiv <ty>, <lhs>, <rhs>`
    ///
    /// # Description
    ///
    /// Performs an **unsigned** division, `lhs / rhs` that must be of type `ty`,
    /// the result is then put in `<res>`. The type must be an integer type and
    /// **only works with unsigned integer types.**
    ///
    /// ## Undefined behavior
    ///
    /// A division by zero (`rhs == 0`), is an undefined behavior and the result
    /// is a poison value.
    Udiv {
        res: Reg,
        ty: FcType,
        lhs: Arg,
        rhs: Arg,
    },
    /// # Syntax
    ///
    /// `<res> = sdiv <ty>, <lhs>, <rhs>`
    ///
    /// # Description
    ///
    /// Performs an **signed** division, `lhs / rhs` that must be of type `ty`,
    /// the result is then put in `<res>`. The type must be an integer type and
    /// **only works with signed integer types.**
    ///
    /// ## Undefined behavior
    ///
    /// A division by zero (`rhs == 0`), is an undefined behavior and the result
    /// is a poison value. It is also an undefined behavior if there is an
    /// overflow, the result would also be a poison value.
    Sdiv {
        res: Reg,
        ty: FcType,
        lhs: Arg,
        rhs: Arg,
    },
    /// # Syntax
    ///
    /// `<res> = fdiv <ty>, <lhs>, <rhs>`
    ///
    /// # Description
    ///
    /// Performs a floating point division, `lhs / rhs` that must be
    /// of type `ty`, the result is then put in `<res>`. The type must be a
    /// floating point type.
    Fdiv {
        res: Reg,
        ty: FcType,
        lhs: Arg,
        rhs: Arg,
    },
    /// # Syntax
    ///
    /// `<res> = urem <ty>, <lhs>, <rhs>`
    ///
    /// # Description
    ///
    /// Performs an **unsigned** remainder (computes the remainder of the
    /// division `lhs / rhs`), `lhs % rhs` that must be of type `ty`, the result
    /// is then put in `<res>`. The type must be an integer type and **only
    /// works with unsigned integer types.**
    ///
    /// ## Undefined behavior
    ///
    /// A remainder by zero (`rhs == 0`), is an undefined behavior and the result
    /// is a poison value.
    Urem {
        res: Reg,
        ty: FcType,
        lhs: Arg,
        rhs: Arg,
    },
    /// # Syntax
    ///
    /// `<res> = srem <ty>, <lhs>, <rhs>`
    ///
    /// # Description
    ///
    /// Performs an **signed** remainder (computes the remainder of the division
    /// `lhs / rhs`), `lhs % rhs` that must be of type `ty`, the result is then
    /// put in `<res>`. The type must be an integer type and **only works with
    /// signed integer types.**
    ///
    /// ## Undefined behavior
    ///
    /// A remainder by zero (`rhs == 0`), is an undefined behavior and the result
    /// is a poison value. It is also an undefined behavior if there is an
    /// overflow, the result would also be a poison value.
    Srem {
        res: Reg,
        ty: FcType,
        lhs: Arg,
        rhs: Arg,
    },
    /// # Syntax
    ///
    /// `<res> = frem <ty>, <lhs>, <rhs>`
    ///
    /// # Description
    ///
    /// Performs a floating point remainder (computes the remainder of the
    /// division `lhs / rhs`), `lhs / rhs` that must be of type `ty`, the result
    /// is then put in `<res>`. The type must be a floating point type.
    Frem {
        res: Reg,
        ty: FcType,
        lhs: Arg,
        rhs: Arg,
    },
    /// # Syntax
    ///
    /// `<res> = and <ty>, <lhs>, <rhs>`
    ///
    /// # Description
    ///
    /// Performs a bitwise and, `lhs & rhs` that must be of type `ty`, the result
    /// is then put in `<res>`. The type must be an integer type and works for
    /// both signed and unsigned integer types, `iNN` / `uNN`.
    And {
        res: Reg,
        ty: FcType,
        lhs: Arg,
        rhs: Arg,
    },
    /// # Syntax
    ///
    /// `<res> = xor <ty>, <lhs>, <rhs>`
    ///
    /// # Description
    ///
    /// Performs a bitwise xor, `lhs ^ rhs` that must be of type `ty`, the result
    /// is then put in `<res>`. The type must be an integer type and works for
    /// both signed and unsigned integer types, `iNN` / `uNN`.
    Xor {
        res: Reg,
        ty: FcType,
        lhs: Arg,
        rhs: Arg,
    },
    /// # Syntax
    ///
    /// `<res> = or <ty>, <lhs>, <rhs>`
    ///
    /// # Description
    ///
    /// Performs a bitwise or, `lhs ^ rhs` that must be of type `ty`, the result
    /// is then put in `<res>`. The type must be an integer type and works for
    /// both signed and unsigned integer types, `iNN` / `uNN`.
    Or {
        res: Reg,
        ty: FcType,
        lhs: Arg,
        rhs: Arg,
    },
    /// # Syntax
    ///
    /// `<res> = shr <ty>, <lhs>, <rhs>`
    ///
    /// # Description
    ///
    /// Performs a shift right, `lhs >> rhs` that must be of type `ty`, the result
    /// is then put in `<res>`. The type must be an integer type and works for
    /// both signed and unsigned integer types, `iNN` / `uNN`.
    Shr {
        res: Reg,
        ty: FcType,
        lhs: Arg,
        rhs: Arg,
    },
    /// # Syntax
    ///
    /// `<res> = shl <ty>, <lhs>, <rhs>`
    ///
    /// # Description
    ///
    /// Performs a shift left, `lhs << rhs` that must be of type `ty`, the result
    /// is then put in `<res>`. The type must be an integer type and works for
    /// both signed and unsigned integer types, `iNN` / `uNN`.
    Shl {
        res: Reg,
        ty: FcType,
        lhs: Arg,
        rhs: Arg,
    },
    /// # Syntax
    ///
    /// `<res> = neg <ty>, <op>`
    ///
    /// # Description
    ///
    /// Performs the negation on the operand and put the result in `<res>`. The
    /// type must be a **signed integer type**.
    Neg { res: Reg, ty: FcType, op: Arg },
    /// # Syntax
    ///
    /// `<res> = fneg <ty>, <op>`
    ///
    /// # Description
    ///
    /// Performs the floating point negation on the operand and put the result
    /// in `<res>`. The type must be a **floating point type**.
    Fneg { res: Reg, ty: FcType, op: Arg },
    /// # Syntax
    ///
    /// `<res> = icmp <cc>, <lhs>, <rhs>`
    ///
    /// # Description
    ///
    /// Performs the `<cc>` comparison on `lhs` and `rhs`, the result is then
    /// put in `<res>`. The type must be an integer type and works for both
    /// signed and unsigned integer types, `iNN` / `uNN`.
    Icmp {
        res: Reg,
        cc: IntCC,
        lhs: Arg,
        rhs: Arg,
    },
    /// # Syntax
    ///
    /// `<res> = salloc <ty> [ * <NumElems> ], align <alignment>`
    ///
    /// # Description
    ///
    /// Allocates `sizeof(<ty>) * NumElems` bytes of memory on the stack and
    /// puts the pointer (with the provided type) of the allocated memory in
    /// `<res>`. The memory is aligned with the given `<alignment>`, that must
    /// be a power of 2 and not zero.
    ///
    /// The memory after allocating it is uninitialized, and loading from
    /// it produces an undefined value. The allocated memory by `salloc` is
    /// automatically released when the function returns.
    Salloc {
        res: Reg,
        ty: FcType,
        num_elems: Option<u32>,
        alignment: Alignment,
    },
    /// # Syntax
    ///
    /// `<res> = load <ty>, ptr <pointer>`
    ///
    /// # Description
    ///
    /// Loads a value of type `<ty>` from memory at location `<pointer>`, and
    /// puts the result in `<res>`. When `<pointer>` is the null pointer the
    /// behavior is undefined, and the result is also undefined.
    ///
    /// - `pointer` must be of type `pointer` and it's pointee must be the same
    ///   type as `ty`.
    Load { res: Reg, ty: FcType, pointer: Arg },
    /// # Syntax
    ///
    /// `store <ty> <val>, ptr <pointer>`
    ///
    /// # Description
    ///
    /// The content of the memory is updated to store `<val>` at the location
    /// `<pointer>`, if `<pointer>` is the null pointer the behavior is
    /// undefined. `<val>` must be of type `<ty>`.
    Store { ty: FcType, val: Arg, pointer: Arg },
}

/// Integer Comparison code
///
/// | Unsigned | Signed | Description              |
/// |----------|--------|--------------------------|
/// | Eq       | Eq     | Equality                 |
/// | Ne       | Ne     | Non-equality             |
/// | Ult      | Slt    | Less than                |
/// | Ule      | Sle    | Less than or equal to    |
/// | Ugt      | Sgt    | Greater than             |
/// | Uge      | Sge    | Greater than or equal to |
#[derive(Debug, Clone)]
pub enum IntCC {
    /// Equal cmp
    Eq,
    /// Non-equal cmp
    Ne,
    /// Signed less than cmp
    Slt,
    /// Signed less than or equal to cmp
    Sle,
    /// Signed greater than cmp
    Sgt,
    /// Signed greater than or equal to
    Sge,
    /// Unsigned less than cmp
    Ult,
    /// Unsigned less than or equal to cmp
    Ule,
    /// Unsigned greater than cmp
    Ugt,
    /// Unsigned greater than or equal to cmp
    Uge,
}

impl Display for IntCC {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            IntCC::Eq => write!(f, "eq"),
            IntCC::Ne => write!(f, "ne"),
            IntCC::Slt => write!(f, "slt"),
            IntCC::Sle => write!(f, "sle"),
            IntCC::Sgt => write!(f, "sgt"),
            IntCC::Sge => write!(f, "sge"),
            IntCC::Ult => write!(f, "ult"),
            IntCC::Ule => write!(f, "ule"),
            IntCC::Ugt => write!(f, "ugt"),
            IntCC::Uge => write!(f, "uge"),
        }
    }
}

#[inline(always)]
fn display_binop_inst(
    f: &mut fmt::Formatter<'_>,
    res: &Reg,
    name: &str,
    ty: &FcType,
    lhs: &Arg,
    rhs: &Arg,
) -> fmt::Result {
    write!(f, "{res} = {name} {ty}, {lhs}, {rhs}")
}

#[inline(always)]
fn display_unary_inst(
    f: &mut fmt::Formatter<'_>,
    res: &Reg,
    name: &str,
    ty: &FcType,
    op: &Arg,
) -> fmt::Result {
    write!(f, "{res} = {name} {ty}, {op}")
}

impl Display for Inst {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Inst::Call {
                res,
                ty,
                fnptr,
                args,
            } => {
                write!(f, "{res} = call {ty} {fnptr}(")?;

                for (i, arg) in args.iter().enumerate() {
                    write!(f, "{arg}")?;

                    if i != args.len() - 1 {
                        write!(f, ", ")?;
                    }
                }

                write!(f, ")")?;

                Ok(())
            }
            // Binary operations insts
            Inst::Add { res, ty, lhs, rhs } => display_binop_inst(f, res, "add", ty, lhs, rhs),
            Inst::Fadd { res, ty, lhs, rhs } => display_binop_inst(f, res, "fadd", ty, lhs, rhs),
            Inst::Sub { res, ty, lhs, rhs } => display_binop_inst(f, res, "sub", ty, lhs, rhs),
            Inst::Fsub { res, ty, lhs, rhs } => display_binop_inst(f, res, "fsub", ty, lhs, rhs),
            Inst::Mul { res, ty, lhs, rhs } => display_binop_inst(f, res, "mul", ty, lhs, rhs),
            Inst::Fmul { res, ty, lhs, rhs } => display_binop_inst(f, res, "fmul", ty, lhs, rhs),
            Inst::Udiv { res, ty, lhs, rhs } => display_binop_inst(f, res, "udiv", ty, lhs, rhs),
            Inst::Sdiv { res, ty, lhs, rhs } => display_binop_inst(f, res, "sdiv", ty, lhs, rhs),
            Inst::Fdiv { res, ty, lhs, rhs } => display_binop_inst(f, res, "fdiv", ty, lhs, rhs),
            Inst::Urem { res, ty, lhs, rhs } => display_binop_inst(f, res, "urem", ty, lhs, rhs),
            Inst::Srem { res, ty, lhs, rhs } => display_binop_inst(f, res, "srem", ty, lhs, rhs),
            Inst::Frem { res, ty, lhs, rhs } => display_binop_inst(f, res, "frem", ty, lhs, rhs),
            Inst::And { res, ty, lhs, rhs } => display_binop_inst(f, res, "and", ty, lhs, rhs),
            Inst::Xor { res, ty, lhs, rhs } => display_binop_inst(f, res, "xor", ty, lhs, rhs),
            Inst::Or { res, ty, lhs, rhs } => display_binop_inst(f, res, "or", ty, lhs, rhs),
            Inst::Shr { res, ty, lhs, rhs } => display_binop_inst(f, res, "shr", ty, lhs, rhs),
            Inst::Shl { res, ty, lhs, rhs } => display_binop_inst(f, res, "shl", ty, lhs, rhs),
            // Unary operations insts
            Inst::Neg { res, ty, op } => display_unary_inst(f, res, "neg", ty, op),
            Inst::Fneg { res, ty, op } => display_unary_inst(f, res, "fneg", ty, op),
            // comparisons
            Inst::Icmp { res, cc, lhs, rhs } => {
                write!(f, "{res} = icmp {cc}, {lhs}, {rhs}")
            }
            // memory operations
            Inst::Salloc {
                res,
                ty,
                num_elems,
                alignment,
            } => {
                write!(f, "{res} = salloc {ty}")?;

                if let Some(num_elems) = num_elems {
                    write!(f, " * {num_elems}")?;
                }

                write!(f, ", align {alignment}")?;

                Ok(())
            }
            Inst::Load { res, ty, pointer } => {
                write!(f, "{res} = load {ty}, ptr {pointer}")
            }
            Inst::Store { ty, val, pointer } => {
                write!(f, "store {ty} {val}, ptr {pointer}")
            }
        }
    }
}

/// A register in FIR, it is a place to store the result of an instruction and
/// can also be used as an [`Arg`], takes the form `%NN` where `NN` is the index
/// and starts at 1.
#[repr(transparent)]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Reg(NonZeroU32);

impl Reg {
    /// Create a new register instance
    #[track_caller]
    pub const fn new(idx: u32) -> Reg {
        Reg(NonZeroU32::new(idx).expect("non zero index for a register"))
    }
}

impl Display for Reg {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "%{}", self.0)
    }
}

/// A terminator is the last instruction of the [basic block], and must branch
/// out.
///
/// [basic block]: crate::BasicBlock
#[derive(Debug, Clone)]
pub enum Terminator {
    /// # Syntax
    ///
    /// `br <cond>, then <true_br>( <true block args> ), else <false_br>( <false block args> )`
    ///
    /// # Description
    ///
    /// This instruction evaluates the `<cond>`, then branch to `<true_br>` if
    /// it evaluated to `true` with the `<true block args>` as block arguments,
    /// or branches to `<else_br>` otherwise with the `<false block args>`.
    ///
    /// - `<cond>` must be of type [`FcType::Bool`].
    /// - `true_br` and `false_br` are Block labels.
    /// - the block arguments `<true block args>` and `<false block args>` must
    ///   have the same types as defined by the block.
    Br {
        cond: Arg,
        true_br: BbLabel,
        true_args: Vec<Arg>,
        false_br: BbLabel,
        false_args: Vec<Arg>,
    },
    /// # Syntax
    ///
    /// `br.icmp <cc>, <lhs>, <rhs>, then <true_br>( <true block args> ), else <false_br>( <false block args> )`
    ///
    /// # Description
    ///
    /// Evaluates the condition given by the condition code on `<lhs>` and
    /// `<rhs>`, then branch to `<true_br>` if it evaluated to `true` with block
    /// arguments `<true block args>`, or to `<else_br>` with block arguments
    /// `<false block args>` otherwise.
    BrIcmp {
        cc: IntCC,
        lhs: Arg,
        rhs: Arg,
        true_br: BbLabel,
        true_args: Vec<Arg>,
        false_br: BbLabel,
        false_args: Vec<Arg>,
    },
    /// # Syntax
    ///
    /// `j <dest>( <block args> )`
    ///
    /// # Description
    ///
    /// This instruction unconditionally branch to `<dest>` block with
    /// `<block args>` as block arguments.
    Jump { dest: BbLabel, args: Vec<Arg> },
    /// # Syntax
    ///
    /// `ret <ty> [val]`
    ///
    /// # Description
    ///
    /// Return the control flow (and a value maybe) back to the caller.
    Ret { ty: FcType, val: Option<Arg> },
}

fn pretty_print_bb_args(f: &mut fmt::Formatter, args: &[Arg]) -> fmt::Result {
    for (i, arg) in args.iter().enumerate() {
        write!(f, "{arg}")?;

        if i != args.len() - 1 {
            write!(f, ", ")?;
        }
    }

    Ok(())
}

impl Display for Terminator {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Terminator::Br {
                cond,
                true_br,
                true_args,
                false_br,
                false_args,
            } => {
                write!(f, "br {cond}, then {true_br}(")?;

                pretty_print_bb_args(f, true_args)?;

                write!(f, "), then {false_br}(")?;

                pretty_print_bb_args(f, false_args)?;
                write!(f, ")")?;

                Ok(())
            }
            Terminator::BrIcmp {
                cc,
                lhs,
                rhs,
                true_br,
                true_args,
                false_br,
                false_args,
            } => {
                write!(f, "br.icmp {cc}, {lhs}, {rhs}, then {true_br}(")?;

                pretty_print_bb_args(f, true_args)?;

                write!(f, "), else {false_br}(")?;

                pretty_print_bb_args(f, false_args)?;
                write!(f, ")")?;

                Ok(())
            }
            Terminator::Jump { dest, args } => {
                write!(f, "j {dest}(")?;
                pretty_print_bb_args(f, args)?;
                write!(f, ")")?;

                Ok(())
            }
            Terminator::Ret { ty, val } => {
                write!(f, "ret {ty}")?;

                if let Some(val) = val {
                    write!(f, ", {val}")?;
                }

                Ok(())
            }
        }
    }
}

impl PrettyDump for Terminator {
    fn try_dump(&self, ctx: &mut PrettyCtxt) -> io::Result<()> {
        write!(ctx.out, "{self}")
    }
}
