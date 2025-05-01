//! Bytecode of lun.

use lun_utils::{
    read_dword, read_many, read_qword, read_word, write_dword, write_qword, write_word,
};

#[repr(u8)]
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum OpCode {
    /// Return from the current function.
    ///
    /// # Format
    ///
    /// ```text
    /// [  ret   ]
    /// ^ opcode
    /// ```
    ///
    /// The size of this instruction is 8 bits, 1 byte.
    Ret = 0,
    // TODO: for SECURITY reasons we should try to avoid offsets and have an
    // index so it's not possible to take a small part of something and so the
    // `const` instruction could just be:
    //
    // [ const  ][      24 bit index      ]
    // ^ 8bit    ^ 24 bit index => 32 bits, 24 bit less in the bytecode.
    //
    // and if we really need to, add a `longconst`, long const to load with a 56 bit index.
    /// Loads a constant from the data pool on the top of the stack with an
    /// offset and a size
    ///
    /// # Format
    ///
    /// ```text
    /// [ const  ][         32-bit offset          ][   16bit size   ]
    /// ^ opcode  ^ offset in the datapool          ^ the size of the
    ///                                              constant to load
    /// ```
    ///
    /// The size of this instruction is 56 bits, 7 bytes.
    Const = 1,
    /// Negates the integers at the top of the stack.
    ///
    /// # Format
    ///
    /// ```text
    /// [  neg   ]
    /// ^ opcode
    /// ```
    ///
    /// The size of this instruction is 8 bits, 1 byte.
    Neg = 2,
    /// Add the two integers at the top of the stack and pushes the result.
    ///
    /// # Format
    ///
    /// ```text
    /// [  add   ]
    /// ^ opcode
    /// ```
    ///
    /// The size of this instruction is 8 bits, 1 byte.
    Add = 3,
    /// Subtracts the two integers at the top of the stack and pushes the result
    ///
    /// # Format
    ///
    /// ```text
    /// [  sub   ]
    /// ^ opcode
    /// ```
    ///
    /// The size of this instruction is 8 bits, 1 byte.
    Sub = 4,
    /// Multiplies the two integers at the top of the stack and pushes the result.
    ///
    /// # Format
    ///
    /// ```text
    /// [  mul   ]
    /// ^ opcode
    /// ```
    ///
    /// The size of this instruction is 8 bits, 1 byte.
    Mul = 5,
    /// Divides the two integers at the top of the stack and pushes the result.
    ///
    /// # Format
    ///
    /// ```text
    /// [  add   ]
    /// ^ opcode
    /// ```
    ///
    /// The size of this instruction is 8 bits, 1 byte.
    Div = 6,
}

impl OpCode {
    /// Mnemonic for `ret` opcode.
    pub const RET_OP: &str = "ret";
    /// Mnemonic for `const` opcode.
    pub const CONST_OP: &str = "const";
    /// Mnemonic for `neg` opcode.
    pub const NEG_OP: &str = "neg";
    /// Mnemonic for `add` opcode.
    pub const ADD_OP: &str = "add";
    /// Mnemonic for `sub` opcode.
    pub const SUB_OP: &str = "sub";
    /// Mnemonic for `mul` opcode.
    pub const MUL_OP: &str = "mul";
    /// Mnemonic for `div` opcode.
    pub const DIV_OP: &str = "div";

    pub fn from_u8(op: u8) -> Option<OpCode> {
        match op {
            _ if op == OpCode::Ret as u8 => Some(OpCode::Ret),
            _ if op == OpCode::Const as u8 => Some(OpCode::Const),
            _ if op == OpCode::Neg as u8 => Some(OpCode::Neg),
            _ if op == OpCode::Add as u8 => Some(OpCode::Add),
            _ if op == OpCode::Sub as u8 => Some(OpCode::Sub),
            _ if op == OpCode::Mul as u8 => Some(OpCode::Mul),
            _ if op == OpCode::Div as u8 => Some(OpCode::Div),
            _ => None,
        }
    }
}

// TODO: add debug infos, like file names, the span of an instruction in the so
// called file etc..
/// A `blob` is a sequence of bytecode.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct Blob {
    /// the code we will run
    pub code: Vec<u8>,
    /// the data pool, where constants are stored.
    pub dpool: DataPool,
}

impl Blob {
    /// Create a new Blob with 8 bytes pre-allocated.
    pub fn new() -> Blob {
        Blob {
            code: Vec::with_capacity(8),
            dpool: DataPool::new(),
        }
    }

    /// Write a byte(code) to the blob.
    ///
    /// # Safety
    ///
    /// If you push a byte that isn't right / proper bytecode, the VM will
    /// crash or do something unexpected
    ///
    /// You should use the `write_xxx` functions instead of writing mannualy
    /// the bytecode
    pub unsafe fn write_raw(&mut self, byte: u8) {
        self.code.push(byte);
    }

    /// Write a `ret` instruction
    pub fn write_return(&mut self) {
        // SAFETY: we're good it's an existing opcode.
        unsafe {
            self.write_raw(OpCode::Ret as u8);
        }
    }

    /// Write a `const` instruction
    pub fn write_const(&mut self, offset: u32, size: u16) {
        // SAFETY: we're good it's an existing opcode.
        unsafe {
            self.write_raw(OpCode::Const as u8);
            write_dword(&mut self.code, offset);
            write_word(&mut self.code, size);
        }
    }

    /// Write a `ret` instruction
    pub fn write_neg(&mut self) {
        // SAFETY: we're good it's an existing opcode.
        unsafe {
            self.write_raw(OpCode::Neg as u8);
        }
    }

    /// Write a `add` instruction
    pub fn write_add(&mut self) {
        // SAFETY: we're good it's an existing opcode.
        unsafe {
            self.write_raw(OpCode::Add as u8);
        }
    }

    /// Write a `sub` instruction
    pub fn write_sub(&mut self) {
        // SAFETY: we're good it's an existing opcode.
        unsafe {
            self.write_raw(OpCode::Sub as u8);
        }
    }

    /// Write a `mul` instruction
    pub fn write_mul(&mut self) {
        // SAFETY: we're good it's an existing opcode.
        unsafe {
            self.write_raw(OpCode::Mul as u8);
        }
    }

    /// Write a `div` instruction
    pub fn write_div(&mut self) {
        // SAFETY: we're good it's an existing opcode.
        unsafe {
            self.write_raw(OpCode::Div as u8);
        }
    }

    /// Disassemble and print the instructions in a human readable format into
    /// stdout.
    pub fn disassemble(&self, name: &str) {
        // TODO: maybe make the Display implementation the output of `disassemble`.
        // but first `dissassemble` would need to write to a `&dyn Write`.
        // TODO: maybe output the hex of each instruction like objdump does.
        println!("== {name} ==");

        let mut offset = 0;
        while offset < self.code.len() {
            offset = self.disassemble_instruction(offset);
        }
    }

    /// Disassemble a single instruction in the blob at the given offset.
    pub fn disassemble_instruction(&self, offset: usize) -> usize {
        // TODO: maybe do a smart thing like if the len of the blob can fit in
        // 4 hex digits then it's fine but if it can't then try if 8 can do it
        // etc etc and keep the same for every instruction in the disassemble's
        // output
        print!("{:04X?}  ", offset);
        let inst = self.code[offset];
        match OpCode::from_u8(inst).expect("This opcode doesn't exist") {
            OpCode::Ret => self.byte_instruction(OpCode::RET_OP, offset),
            OpCode::Const => {
                let off = read_dword(&self.code, offset + 1) as usize;
                let size = read_word(&self.code, offset + 5) as usize;
                println!("const offset={:X}, size={:X}", off, size,);
                // TODO: this print in little endian format but it could be
                // confusing so maybe print it into big endian, so `0xDEADBEEF`
                // won't show as `[EF, BE, AD, DE, 0, 0, 0, 0]`.
                // but `[0, 0, 0, 0, DE, AD, BE, EF]`.
                println!("      => {:X?}", &self.dpool.data[off..off + size]);
                offset + 7
            }
            OpCode::Neg => self.byte_instruction(OpCode::NEG_OP, offset),
            OpCode::Add => self.byte_instruction(OpCode::ADD_OP, offset),
            OpCode::Sub => self.byte_instruction(OpCode::SUB_OP, offset),
            OpCode::Mul => self.byte_instruction(OpCode::MUL_OP, offset),
            OpCode::Div => self.byte_instruction(OpCode::DIV_OP, offset),
        }
    }

    /// Disassemble an instruction that only fits in one byte (it's common).
    pub(crate) fn byte_instruction(&self, name: &str, offset: usize) -> usize {
        println!("{name}");
        offset + 1
    }
}

/// An immutable pool of data that contains all of the constants of the program
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct DataPool {
    pub(crate) data: Vec<u8>,
}

impl DataPool {
    /// Create a new DataPool with 8 bytes pre-allocated.
    pub fn new() -> DataPool {
        DataPool {
            data: Vec::with_capacity(8),
        }
    }

    /// Write a byte of data to the pool and returns the offset where it was
    /// written
    #[must_use]
    #[inline(always)]
    pub fn write_raw(&mut self, byte: u8) -> usize {
        let offset = self.data.len();
        self.data.push(byte);
        offset
    }

    /// Write an integer (64 bits in lun), to the data pool in little endian
    /// format, and returns an offset where it was written
    #[must_use]
    pub fn write_integer(&mut self, int: u64) -> usize {
        write_qword(&mut self.data, int)
    }

    /// Read a 64-bit little-endian integer from the data pool at the given offset.
    /// Panics if there are not enough bytes to read a full u64.
    pub fn read_integer(&self, offset: u64) -> u64 {
        read_qword(&self.data, offset as usize)
    }

    /// Reads a variable amount of data from the data pool at the given offset
    /// and size. Panics if there are not enough bytes to read a full u64.
    pub fn read_many(&self, offset: usize, size: usize) -> &[u8] {
        read_many(&self.data, offset, size)
    }
}
