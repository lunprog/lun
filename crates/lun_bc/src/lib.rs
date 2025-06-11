//! Bytecode of lun.

use bytemuck::Contiguous;

pub mod bin;

#[repr(u8)]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Contiguous)]
pub enum OpCode {
    /// add.type rd, rs1, rs2
    /// => rd = rs1 + rs2
    Add = 0,

    /// sub.type rd, rs1, rs2
    /// => rd = rs1 - rs2
    Sub = 1,

    /// mul.type rd, rs1, rs2
    /// => rd = rs1 * rs2
    Mul = 2,

    /// div.type rd, rs1, rs2
    /// => rd = rs1 / rs2
    Div = 3,

    /// rem.type rd, rs1, rs2
    /// => rd = rs1 % rs2
    Rem = 4,

    /// clt.type rd, rs1, rs2
    /// => rd = rs1 < rs2
    Clt = 5,

    /// cge.type rd, rs1, rs2
    /// => rd = rs1 >= rs2
    Cge = 6,

    /// ceq.type rd, rs1, rs2
    /// => rd = rs1 == rs2
    Ceq = 7,

    /// cne.type rd, rs1, rs2
    /// => rd = rs1 != rs2
    Cne = 8,

    /// and.type rd, rs1, rs2
    /// => rd = rs1 and rs2
    And = 9,

    /// or.type rd, rs1, rs2
    /// => rd = rs1 or rs2
    Or = 10,

    /// xor.type rd, rs1, rs2
    /// => rd = rs1 xor rs2
    Xor = 11,

    /// call offset
    /// => rsp = rsp - WORD_LEN/8 ; M[rsp] = rs ; pc += sext(offset)
    Call = 12,

    /// ret
    /// => pc = M[rsp] ; rsp = rsp + WORD_LEN/8
    Ret = 13,

    /// jze rs2, offset(rs1)
    /// => if rs == 0 then pc += sext(offset)
    Jze = 14,

    /// beq rs1, rs2, offset
    /// => if rs1 == rs2 then pc += sext(offset)
    Beq = 15,

    /// bne rs1, rs2, offset
    /// => if rs1 != rs2 then pc += sext(offset)
    Bne = 16,

    /// blt rs1, rs2, offset
    /// => if rs1 < rs2 then pc += sext(offset)
    Blt = 17,

    /// bge rs1, rs2, offset
    /// => if rs1 >= rs2 then pc += sext(offset)
    Bge = 18,

    /// ld.b rd, offset(rs)
    /// => rd = M[rs + sext(offset)][7:0]
    LdB = 19,

    /// ld.h rd, offset(rs)
    /// => rd = M[rs + sext(offset)][15:0]
    LdH = 20,

    /// ld.w rd, offset(rs)
    /// => rd = M[rs + sext(offset)][31:0]
    LdW = 21,

    /// ld.d rd, offset(rs)
    /// => rd = M[rs + sext(offset)][63:0]
    LdD = 22,

    /// st.b rs2, offset(rs1)
    /// => M[rs1 + sext(offset)] = rs2[7:0]
    StB = 23,

    /// st.h rs2, offset(rs1)
    /// => M[rs1 + sext(offset)] = rs2[15:0]
    StH = 24,

    /// st.w rs2, offset(rs1)
    /// => M[rs1 + sext(offset)] = rs2[31:0]
    StW = 25,

    /// st.d rs2, offset(rs1)
    /// => M[rs1 + sext(offset)] = rs2[63:0]
    StD = 26,

    /// li.b rd, imm(rs)
    /// => rd = imm[7:0]
    LiB = 27,

    /// li.h rd, imm(rs)
    /// => rd = imm[15:0]
    LiH = 28,

    /// li.w rd, imm(rs)
    /// => rd = imm[31:0]
    LiW = 29,

    /// li.d rd, imm(rs)
    /// => rd = imm[63:0]
    LiD = 30,

    /// mov rd, rs
    /// => rd = rs
    Mov = 31,

    /// push rs
    /// => rsp = rsp - WORD_LEN/8 ; M[rsp] = rs
    Push = 32,

    /// pop rd
    /// => rd = rsp ; rsp = rsp + WORD_LEN/8
    Pop = 33,
}

impl OpCode {
    /// Mnemonic for `add` opcode.
    pub const ADD: &str = "add";
    /// Opcode for `add`
    pub const ADD_OP: usize = 0;

    /// Mnemonic for `sub` opcode.
    pub const SUB: &str = "sub";
    /// Opcode for `sub`
    pub const SUB_OP: usize = 1;

    /// Mnemonic for `mul` opcode.
    pub const MUL: &str = "mul";
    /// Opcode for `mul`
    pub const MUL_OP: usize = 2;

    /// Mnemonic for `div` opcode.
    pub const DIV: &str = "div";
    /// Opcode for `div`
    pub const DIV_OP: usize = 3;

    /// Mnemonic for `rem` opcode.
    pub const REM: &str = "rem";
    /// Opcode for `rem`
    pub const REM_OP: usize = 4;

    /// Mnemonic for `clt` opcode.
    pub const CLT: &str = "clt";
    /// Opcode for `clt`
    pub const CLT_OP: usize = 5;

    /// Mnemonic for `cge` opcode.
    pub const CGE: &str = "cge";
    /// Opcode for `cge`
    pub const CGE_OP: usize = 6;

    /// Mnemonic for `ceq` opcode.
    pub const CEQ: &str = "ceq";
    /// Opcode for `ceq`
    pub const CEQ_OP: usize = 7;

    /// Mnemonic for `cne` opcode.
    pub const CNE: &str = "cne";
    /// Opcode for `cne`
    pub const CNE_OP: usize = 8;

    /// Mnemonic for `and` opcode.
    pub const AND: &str = "and";
    /// Opcode for `and`
    pub const AND_OP: usize = 9;

    /// Mnemonic for `or` opcode.
    pub const OR: &str = "or";
    /// Opcode for `or`
    pub const OR_OP: usize = 10;

    /// Mnemonic for `xor` opcode.
    pub const XOR: &str = "xor";
    /// Opcode for `xor`
    pub const XOR_OP: usize = 11;

    /// Mnemonic for `call` opcode.
    pub const CALL: &str = "call";
    /// Opcode for `call`
    pub const CALL_OP: usize = 12;

    /// Mnemonic for `ret` opcode.
    pub const RET: &str = "ret";
    /// Opcode for `ret`
    pub const RET_OP: usize = 13;

    /// Mnemonic for `jze` opcode.
    pub const JZE: &str = "jze";
    /// Opcode for `jze`
    pub const JZE_OP: usize = 14;

    /// Mnemonic for `beq` opcode.
    pub const BEQ: &str = "beq";
    /// Opcode for `beq`
    pub const BEQ_OP: usize = 15;

    /// Mnemonic for `bne` opcode.
    pub const BNE: &str = "bne";
    /// Opcode for `bne`
    pub const BNE_OP: usize = 16;

    /// Mnemonic for `blt` opcode.
    pub const BLT: &str = "blt";
    /// Opcode for `blt`
    pub const BLT_OP: usize = 17;

    /// Mnemonic for `bge` opcode.
    pub const BGE: &str = "bge";
    /// Opcode for `bge`
    pub const BGE_OP: usize = 18;

    /// Mnemonic for `ld.b` opcode.
    pub const LD_B: &str = "ld.b";
    /// Opcode for `ld.b`
    pub const LD_B_OP: usize = 19;

    /// Mnemonic for `ld.h` opcode.
    pub const LD_H: &str = "ld.h";
    /// Opcode for `ld.h`
    pub const LD_H_OP: usize = 20;

    /// Mnemonic for `ld.w` opcode.
    pub const LD_W: &str = "ld.w";
    /// Opcode for `ld.w`
    pub const LD_W_OP: usize = 21;

    /// Mnemonic for `ld.d` opcode.
    pub const LD_D: &str = "ld.d";
    /// Opcode for `ld.d`
    pub const LD_D_OP: usize = 22;

    /// Mnemonic for `st.b` opcode.
    pub const ST_B: &str = "st.b";
    /// Opcode for `st.b`
    pub const ST_B_OP: usize = 23;

    /// Mnemonic for `st.h` opcode.
    pub const ST_H: &str = "st.h";
    /// Opcode for `st.h`
    pub const ST_H_OP: usize = 24;

    /// Mnemonic for `st.w` opcode.
    pub const ST_W: &str = "st.w";
    /// Opcode for `st.w`
    pub const ST_W_OP: usize = 25;

    /// Mnemonic for `st.d` opcode.
    pub const ST_D: &str = "st.d";
    /// Opcode for `st.d`
    pub const ST_D_OP: usize = 26;

    /// Mnemonic for `li.b` opcode.
    pub const LI_B: &str = "li.b";
    /// Opcode for `li.b`
    pub const LI_B_OP: usize = 27;

    /// Mnemonic for `li.h` opcode.
    pub const LI_H: &str = "li.h";
    /// Opcode for `li.h`
    pub const LI_H_OP: usize = 28;

    /// Mnemonic for `li.w` opcode.
    pub const LI_W: &str = "li.w";
    /// Opcode for `li.w`
    pub const LI_W_OP: usize = 29;

    /// Mnemonic for `li.d` opcode.
    pub const LI_D: &str = "li.d";
    /// Opcode for `li.d`
    pub const LI_D_OP: usize = 30;

    /// Mnemonic for `mov` opcode.
    pub const MOV: &str = "mov";
    /// Opcode for `mov`
    pub const MOV_OP: usize = 31;

    /// Mnemonic for `push` opcode.
    pub const PUSH: &str = "push";
    /// Opcode for `push`
    pub const PUSH_OP: usize = 32;

    /// Mnemonic for `pop` opcode.
    pub const POP: &str = "pop";
    /// Opcode for `pop`
    pub const POP_OP: usize = 33;

    pub fn from_u8(op: u8) -> Option<OpCode> {
        match op {
            _ => None,
        }
    }
}

// TODO: add debug infos, like file names, the span of an instruction in the so
// called file etc..
/// A `BlobBc` is a sequence of bytecode.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct BcBlob {
    /// the code we will run
    pub code: Vec<u8>,
}

impl BcBlob {
    /// Create a new Blob.
    pub fn new() -> BcBlob {
        BcBlob {
            code: Vec::with_capacity(16),
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

    /// Returns the bytes of the byutecode's blob
    pub fn code_data(&self) -> Vec<u8> {
        self.code.clone()
    }

    /// Disassemble and print the instructions in a human readable format into
    /// stdout.
    pub fn disassemble(&self, name: &str) {
        // TODO: maybe make the Display implementation the output of `disassemble`.
        // but first `dissassemble` would need to write to a `&dyn Write`.
        // TODO: maybe output the hex of each instruction like objdump does.
        if !name.is_empty() {
            println!("== {name} ==");
        }

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
            _ => todo!("TODO(URGENT)"),
        }
    }
}
