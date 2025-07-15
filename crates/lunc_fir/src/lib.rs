//! Intermediate Representation of Lun, the closest one to the final assembly
//! or machine code, while still being target independent

use std::{fmt::Display, io};

use lunc_parser::expr::{BinOp, UnaryOp};

#[derive(Debug, Clone)]
pub struct IrUnit {
    functions: Vec<Fun>,
    /// read-only data
    rodata: Vec<u8>,
}

impl IrUnit {
    pub fn new() -> IrUnit {
        IrUnit {
            functions: Vec::new(),
            rodata: Vec::new(),
        }
    }

    pub fn push_rodata(&mut self, data: impl AsRef<[u8]>) -> usize {
        let off = self.rodata.len();

        self.rodata.extend_from_slice(data.as_ref());
        off
    }

    pub fn push_fun(&mut self, fun: Fun) {
        self.functions.push(fun);
    }

    /// Dump ir to stdout
    pub fn dump(&self) -> io::Result<()> {
        self.dump_with(&mut io::stdout())
    }

    /// Dump ir, write to the provided writer
    pub fn dump_with(&self, mut out: impl io::Write) -> io::Result<()> {
        out.flush()?;

        writeln!(out, "==== Function ====")?;
        writeln!(out)?;

        for fun in &self.functions {
            fun.dump_with(&mut out)?;
        }

        if !self.rodata.is_empty() {
            writeln!(out)?;
            writeln!(out, "==== Rodata ====")?;
            writeln!(out)?;
            self.dump_rodata(&mut out)?;
        }

        Ok(())
    }

    pub fn dump_rodata(&self, mut out: impl io::Write) -> io::Result<()> {
        writeln!(
            out,
            "  OFFSET  | 00 01 02 03  04 05 06 07  08 09 0A 0B  0C 0D 0E 0F |      ASCII       |"
        )?;
        let chunks = self.rodata.chunks(16);

        for (i, chunk) in chunks.clone().enumerate() {
            // Offset
            write!(out, " {:8X} |", i * 16)?;

            // Hexadecimal bytes
            for (j, byte) in chunk.iter().enumerate() {
                if j != 0 && j % 4 == 0 {
                    write!(out, " ")?;
                }
                write!(out, " {byte:02X}")?;
            }
            if chunk.len() % 4 == 0 && i == chunks.len() - 1 {
                write!(out, " ")?;
            }

            // Align if less than 16 bytes
            let remaining = 16 - chunk.len();
            if remaining > 0 {
                // Calculate how many gaps to insert
                for j in 0..remaining {
                    if (chunk.len() + j) % 4 == 0 && j != 0 {
                        write!(out, " ")?;
                    }
                    write!(out, "   ")?;
                }
            }

            write!(out, " | ")?;

            // ASCII representation
            for byte in chunk {
                let ch = *byte;
                if ch.is_ascii_graphic() || ch == b' ' {
                    write!(out, "{}", ch as char)?;
                } else {
                    write!(out, ".")?;
                }
            }

            // Align if less than 16 bytes
            for _ in 0..(16 - chunk.len()) {
                write!(out, ".")?;
            }

            writeln!(out, " |")?;
        }

        Ok(())
    }
}

impl Default for IrUnit {
    fn default() -> Self {
        IrUnit::new()
    }
}

type AtomicType = String;

/// Function
#[derive(Debug, Clone)]
pub struct Fun {
    /// un mangled name of the function
    pub name: String,
    /// arguments types
    pub args: Vec<AtomicType>,
    /// return type
    pub ret: AtomicType,
    /// body of the function composed of a list of blocks.
    pub body: Vec<OpBlock>,
}

impl Fun {
    pub fn dump_with(&self, mut out: impl io::Write) -> io::Result<()> {
        let Fun {
            name,
            args,
            ret,
            body,
        } = self;

        write!(out, "{name}(")?;
        for (i, arg) in args.iter().enumerate() {
            write!(out, "{arg}")?;

            if i != args.len() - 1 {
                write!(out, ", ")?;
            }
        }
        write!(out, ")")?;
        writeln!(out, " -> {ret}")?;
        // TODO: dump var like this
        // -> var[1]: u8

        writeln!(out, "{{")?;

        for (i, block) in body.iter().enumerate() {
            writeln!(out, ".b{i}:")?;
            block.dump_with(&mut out)?;
        }

        writeln!(out, "}}")?;

        Ok(())
    }
}

/// A variable index. Every variable index must be greater than 0, because the
/// zero variable index is special
#[derive(Debug, Clone)]
pub struct VarIndex(u64);

impl VarIndex {
    pub const ZERO: VarIndex = VarIndex(0);

    pub fn to_usize(&self) -> usize {
        self.0 as usize
    }
}

impl Display for VarIndex {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        Display::fmt(&self.0, f)
    }
}

/// Argument
#[derive(Debug, Clone)]
pub enum Arg {
    Var(VarIndex),
    IntegerLiteral(u32),
    Symbol(String),
    /// An offset in the read-only data.
    RoData(u64),
}

impl Arg {
    pub fn dump_with(&self, mut out: impl io::Write) -> io::Result<()> {
        match self {
            Arg::Var(idx) => write!(out, "var[{idx}]")?,
            Arg::IntegerLiteral(i) => write!(out, "{i}")?,
            Arg::Symbol(name) => write!(out, "{name}")?,
            Arg::RoData(offset) => write!(out, "data[{offset}]")?,
        }

        Ok(())
    }
}

/// A block is a list of [`Op`] that MUST end with a terminal operation.
#[derive(Debug, Clone)]
pub struct OpBlock {
    ops: Vec<Op>,
    finished: bool,
}

impl OpBlock {
    pub fn new() -> OpBlock {
        OpBlock {
            ops: Vec::new(),
            finished: false,
        }
    }

    pub fn finish(&mut self) {
        assert!(
            self.ops
                .last()
                .expect("a block require at least one operation")
                .is_terminating(),
            "a block must finish with a terminating operation at the end"
        );
        self.finished = true;
    }

    pub fn push(&mut self, op: Op) {
        assert!(
            !self.finished,
            "cannot push an operation on a finished block"
        );
        self.ops.push(op);
    }

    pub fn dump_with(&self, mut out: impl io::Write) -> io::Result<()> {
        for op in &self.ops {
            match op {
                Op::LoadArgToVar { index, val } => {
                    writeln!(out, "    var[{index}] = ")?;
                    val.dump_with(&mut out)?;
                }
                Op::TemporaryAssign { index, val } => {
                    writeln!(out, "    ${index} = ")?;
                    val.dump_with(&mut out)?;
                }
                Op::Fallthrough => {
                    writeln!(out, "    fallthrough")?;
                }
                Op::Branch {
                    arg,
                    true_branch,
                    false_branch,
                } => {
                    write!(out, "    branch ")?;
                    arg.dump_with(&mut out)?;
                    writeln!(out, ", .{true_branch} else .{false_branch}")?;
                }
                Op::Return { arg } => {
                    write!(out, "    return")?;

                    if let Some(arg) = arg {
                        write!(out, " ")?;
                        arg.dump_with(&mut out)?;
                    }

                    writeln!(out)?;
                }
            }
        }
        Ok(())
    }
}

impl Default for OpBlock {
    fn default() -> Self {
        OpBlock::new()
    }
}

/// Operation
#[derive(Debug, Clone)]
pub enum Op {
    /// ```text
    /// var[index] = val
    /// ```
    LoadArgToVar { index: VarIndex, val: Value },
    /// ```text
    /// $index = val
    /// ```
    TemporaryAssign { index: u64, val: Arg },
    /// ```text
    /// falthrough
    /// ```
    ///
    /// falls through the following block (it is a no-op in most platforms, so
    /// no cost)
    Fallthrough,
    /// ```text
    /// branch arg, .true_branch else .false_branch
    /// ```
    ///
    /// evaluates `arg` then jumps to `.true_branch` if arg == 0, or jumps to
    /// `.false_branch` if arg != 0,
    Branch {
        arg: Arg,
        /// block index in function
        true_branch: u64,
        /// block index in function
        false_branch: u64,
    },
    /// ```text
    /// return arg?
    /// ```
    ///
    /// returns the function with the provided value, may be nothing if, return
    /// type is void.
    Return { arg: Option<Arg> },
}

impl Op {
    pub fn is_terminating(&self) -> bool {
        matches!(
            self,
            Op::Fallthrough | Op::Branch { .. } | Op::Return { .. }
        )
    }
}

/// Value
#[derive(Debug, Clone)]
pub enum Value {
    /// ```text
    /// arg
    /// ```
    Arg(Arg),
    /// ```text
    /// lhs op rhs
    /// ```
    Binary { lhs: Arg, op: BinOp, rhs: Arg },
    /// ```text
    /// op arg
    /// ```
    Unary { op: UnaryOp, arg: Arg },
    /// ```text
    /// call(fun, args..)
    /// ```
    Call { fun: Arg, args: Vec<Arg> },
}

impl Value {
    pub fn dump_with(&self, mut out: impl io::Write) -> io::Result<()> {
        match self {
            Value::Arg(arg) => {
                arg.dump_with(&mut out)?;
            }
            Value::Binary { lhs, op, rhs } => {
                lhs.dump_with(&mut out)?;
                write!(out, " {op} ")?;
                rhs.dump_with(&mut out)?;
            }
            Value::Unary { op, arg } => {
                write!(out, "{op} ")?;
                arg.dump_with(&mut out)?;
            }
            Value::Call { fun, args } => {
                write!(out, "call(")?;

                fun.dump_with(&mut out)?;

                for arg in args {
                    write!(out, ", ")?;
                    arg.dump_with(&mut out)?;
                }

                write!(out, ")")?;
            }
        }
        Ok(())
    }
}
