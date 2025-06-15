//! Bytecode of lun.

use std::fmt::Display;

use bytemuck::Contiguous;
use lun_utils::{read_dword, read_half, read_word, write_dword, write_half, write_word};

pub mod bin;

#[repr(u8)]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Contiguous)]
pub enum Opcode {
    /// add.funct rd, rs1, rs2
    /// => rd = rs1 + rs2
    Add = 0,

    /// sub.funct rd, rs1, rs2
    /// => rd = rs1 - rs2
    Sub = 1,

    /// mul.funct rd, rs1, rs2
    /// => rd = rs1 * rs2
    Mul = 2,

    /// div.funct rd, rs1, rs2
    /// => rd = rs1 / rs2
    Div = 3,

    /// rem.funct rd, rs1, rs2
    /// => rd = rs1 % rs2
    Rem = 4,

    /// clt.funct rd, rs1, rs2
    /// => rd = rs1 < rs2
    Clt = 5,

    /// cge.funct rd, rs1, rs2
    /// => rd = rs1 >= rs2
    Cge = 6,

    /// ceq.funct rd, rs1, rs2
    /// => rd = rs1 == rs2
    Ceq = 7,

    /// cne.funct rd, rs1, rs2
    /// => rd = rs1 != rs2
    Cne = 8,

    /// and.funct rd, rs1, rs2
    /// => rd = rs1 and rs2
    And = 9,

    /// or.funct rd, rs1, rs2
    /// => rd = rs1 or rs2
    Or = 10,

    /// xor.funct rd, rs1, rs2
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

impl Opcode {
    /// Mnemonic for `add` opcode.
    pub const ADD: &str = "add";
    /// Opcode for `add`
    pub const ADD_OP: u8 = 0;

    /// Mnemonic for `sub` opcode.
    pub const SUB: &str = "sub";
    /// Opcode for `sub`
    pub const SUB_OP: u8 = 1;

    /// Mnemonic for `mul` opcode.
    pub const MUL: &str = "mul";
    /// Opcode for `mul`
    pub const MUL_OP: u8 = 2;

    /// Mnemonic for `div` opcode.
    pub const DIV: &str = "div";
    /// Opcode for `div`
    pub const DIV_OP: u8 = 3;

    /// Mnemonic for `rem` opcode.
    pub const REM: &str = "rem";
    /// Opcode for `rem`
    pub const REM_OP: u8 = 4;

    /// Mnemonic for `clt` opcode.
    pub const CLT: &str = "clt";
    /// Opcode for `clt`
    pub const CLT_OP: u8 = 5;

    /// Mnemonic for `cge` opcode.
    pub const CGE: &str = "cge";
    /// Opcode for `cge`
    pub const CGE_OP: u8 = 6;

    /// Mnemonic for `ceq` opcode.
    pub const CEQ: &str = "ceq";
    /// Opcode for `ceq`
    pub const CEQ_OP: u8 = 7;

    /// Mnemonic for `cne` opcode.
    pub const CNE: &str = "cne";
    /// Opcode for `cne`
    pub const CNE_OP: u8 = 8;

    /// Mnemonic for `and` opcode.
    pub const AND: &str = "and";
    /// Opcode for `and`
    pub const AND_OP: u8 = 9;

    /// Mnemonic for `or` opcode.
    pub const OR: &str = "or";
    /// Opcode for `or`
    pub const OR_OP: u8 = 10;

    /// Mnemonic for `xor` opcode.
    pub const XOR: &str = "xor";
    /// Opcode for `xor`
    pub const XOR_OP: u8 = 11;

    /// Mnemonic for `call` opcode.
    pub const CALL: &str = "call";
    /// Opcode for `call`
    pub const CALL_OP: u8 = 12;

    /// Mnemonic for `ret` opcode.
    pub const RET: &str = "ret";
    /// Opcode for `ret`
    pub const RET_OP: u8 = 13;

    /// Mnemonic for `jze` opcode.
    pub const JZE: &str = "jze";
    /// Opcode for `jze`
    pub const JZE_OP: u8 = 14;

    /// Mnemonic for `beq` opcode.
    pub const BEQ: &str = "beq";
    /// Opcode for `beq`
    pub const BEQ_OP: u8 = 15;

    /// Mnemonic for `bne` opcode.
    pub const BNE: &str = "bne";
    /// Opcode for `bne`
    pub const BNE_OP: u8 = 16;

    /// Mnemonic for `blt` opcode.
    pub const BLT: &str = "blt";
    /// Opcode for `blt`
    pub const BLT_OP: u8 = 17;

    /// Mnemonic for `bge` opcode.
    pub const BGE: &str = "bge";
    /// Opcode for `bge`
    pub const BGE_OP: u8 = 18;

    /// Mnemonic for `ld.b` opcode.
    pub const LD_B: &str = "ld.b";
    /// Opcode for `ld.b`
    pub const LD_B_OP: u8 = 19;

    /// Mnemonic for `ld.h` opcode.
    pub const LD_H: &str = "ld.h";
    /// Opcode for `ld.h`
    pub const LD_H_OP: u8 = 20;

    /// Mnemonic for `ld.w` opcode.
    pub const LD_W: &str = "ld.w";
    /// Opcode for `ld.w`
    pub const LD_W_OP: u8 = 21;

    /// Mnemonic for `ld.d` opcode.
    pub const LD_D: &str = "ld.d";
    /// Opcode for `ld.d`
    pub const LD_D_OP: u8 = 22;

    /// Mnemonic for `st.b` opcode.
    pub const ST_B: &str = "st.b";
    /// Opcode for `st.b`
    pub const ST_B_OP: u8 = 23;

    /// Mnemonic for `st.h` opcode.
    pub const ST_H: &str = "st.h";
    /// Opcode for `st.h`
    pub const ST_H_OP: u8 = 24;

    /// Mnemonic for `st.w` opcode.
    pub const ST_W: &str = "st.w";
    /// Opcode for `st.w`
    pub const ST_W_OP: u8 = 25;

    /// Mnemonic for `st.d` opcode.
    pub const ST_D: &str = "st.d";
    /// Opcode for `st.d`
    pub const ST_D_OP: u8 = 26;

    /// Mnemonic for `li.b` opcode.
    pub const LI_B: &str = "li.b";
    /// Opcode for `li.b`
    pub const LI_B_OP: u8 = 27;

    /// Mnemonic for `li.h` opcode.
    pub const LI_H: &str = "li.h";
    /// Opcode for `li.h`
    pub const LI_H_OP: u8 = 28;

    /// Mnemonic for `li.w` opcode.
    pub const LI_W: &str = "li.w";
    /// Opcode for `li.w`
    pub const LI_W_OP: u8 = 29;

    /// Mnemonic for `li.d` opcode.
    pub const LI_D: &str = "li.d";
    /// Opcode for `li.d`
    pub const LI_D_OP: u8 = 30;

    /// Mnemonic for `mov` opcode.
    pub const MOV: &str = "mov";
    /// Opcode for `mov`
    pub const MOV_OP: u8 = 31;

    /// Mnemonic for `push` opcode.
    pub const PUSH: &str = "push";
    /// Opcode for `push`
    pub const PUSH_OP: u8 = 32;

    /// Mnemonic for `pop` opcode.
    pub const POP: &str = "pop";
    /// Opcode for `pop`
    pub const POP_OP: u8 = 33;
}

#[repr(u8)]
#[allow(non_camel_case_types)]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Contiguous)]
pub enum Reg {
    zr = 0,
    a0 = 1,
    a1 = 2,
    a2 = 3,
    a3 = 4,
    a4 = 5,
    t0 = 6,
    t1 = 7,
    t2 = 8,
    t3 = 9,
    s0 = 10,
    s1 = 11,
    s2 = 12,
    s3 = 13,
    fp = 14,
    sp = 15,
}

impl Display for Reg {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::zr => f.write_str("zr"),
            Self::a0 => f.write_str("a0"),
            Self::a1 => f.write_str("a1"),
            Self::a2 => f.write_str("a2"),
            Self::a3 => f.write_str("a3"),
            Self::a4 => f.write_str("a4"),
            Self::t0 => f.write_str("t0"),
            Self::t1 => f.write_str("t1"),
            Self::t2 => f.write_str("t2"),
            Self::t3 => f.write_str("t3"),
            Self::s0 => f.write_str("s0"),
            Self::s1 => f.write_str("s1"),
            Self::s2 => f.write_str("s2"),
            Self::s3 => f.write_str("s3"),
            Self::fp => f.write_str("fp"),
            Self::sp => f.write_str("sp"),
        }
    }
}

/// Arithmetic function
#[repr(u8)]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Contiguous)]
pub enum AFunct {
    X = 0,
    F16 = 1,
    F32 = 2,
    F64 = 3,
}

impl Display for AFunct {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::X => f.write_str("x"),
            Self::F16 => f.write_str("f16"),
            Self::F32 => f.write_str("f32"),
            Self::F64 => f.write_str("f64"),
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

    fn write_arithmetic_inst(&mut self, opcode: u8, funct: AFunct, rd: Reg, rs1: Reg, rs2: Reg) {
        // opcode
        self.code.push(opcode);
        // funct and rd
        let funct_rd = (funct as u8) << 4 | rd as u8;
        self.code.push(funct_rd);
        // rs1 and rs2
        let rs1_rs2 = (rs1 as u8) << 4 | rs2 as u8;
        self.code.push(rs1_rs2);
    }

    /// Write `add` inst
    pub fn write_add(&mut self, typ: AFunct, rd: Reg, rs1: Reg, rs2: Reg) {
        self.write_arithmetic_inst(Opcode::ADD_OP, typ, rd, rs1, rs2);
    }
    /// Write `sub` inst
    pub fn write_sub(&mut self, typ: AFunct, rd: Reg, rs1: Reg, rs2: Reg) {
        self.write_arithmetic_inst(Opcode::SUB_OP, typ, rd, rs1, rs2);
    }

    /// Write `mul` inst
    pub fn write_mul(&mut self, typ: AFunct, rd: Reg, rs1: Reg, rs2: Reg) {
        self.write_arithmetic_inst(Opcode::MUL_OP, typ, rd, rs1, rs2);
    }

    /// Write `div` inst
    pub fn write_div(&mut self, typ: AFunct, rd: Reg, rs1: Reg, rs2: Reg) {
        self.write_arithmetic_inst(Opcode::DIV_OP, typ, rd, rs1, rs2);
    }

    /// Write `rem` inst
    pub fn write_rem(&mut self, typ: AFunct, rd: Reg, rs1: Reg, rs2: Reg) {
        self.write_arithmetic_inst(Opcode::REM_OP, typ, rd, rs1, rs2);
    }

    /// Write `clt` inst
    pub fn write_clt(&mut self, typ: AFunct, rd: Reg, rs1: Reg, rs2: Reg) {
        self.write_arithmetic_inst(Opcode::CLT_OP, typ, rd, rs1, rs2);
    }

    /// Write `cge` inst
    pub fn write_cge(&mut self, typ: AFunct, rd: Reg, rs1: Reg, rs2: Reg) {
        self.write_arithmetic_inst(Opcode::CGE_OP, typ, rd, rs1, rs2);
    }

    /// Write `ceq` inst
    pub fn write_ceq(&mut self, typ: AFunct, rd: Reg, rs1: Reg, rs2: Reg) {
        self.write_arithmetic_inst(Opcode::CEQ_OP, typ, rd, rs1, rs2);
    }

    /// Write `cne` inst
    pub fn write_cne(&mut self, typ: AFunct, rd: Reg, rs1: Reg, rs2: Reg) {
        self.write_arithmetic_inst(Opcode::CNE_OP, typ, rd, rs1, rs2);
    }

    /// Write `and` inst
    pub fn write_and(&mut self, typ: AFunct, rd: Reg, rs1: Reg, rs2: Reg) {
        self.write_arithmetic_inst(Opcode::AND_OP, typ, rd, rs1, rs2);
    }

    /// Write `or` inst
    pub fn write_or(&mut self, typ: AFunct, rd: Reg, rs1: Reg, rs2: Reg) {
        self.write_arithmetic_inst(Opcode::OR_OP, typ, rd, rs1, rs2);
    }

    /// Write `xor` inst
    pub fn write_xor(&mut self, typ: AFunct, rd: Reg, rs1: Reg, rs2: Reg) {
        self.write_arithmetic_inst(Opcode::XOR_OP, typ, rd, rs1, rs2);
    }

    /// Write `call` inst
    pub fn write_call(&mut self, imm: u32) {
        // opcode
        self.code.push(Opcode::CALL_OP);
        // imm
        write_word(&mut self.code, imm);
    }

    /// Write `ret` inst
    pub fn write_ret(&mut self) {
        // opcode
        self.code.push(Opcode::RET_OP);
    }

    /// opcode | reg1 | reg2
    /// 8b     | 4b   | 4b   } 16b
    fn write_reg_reg(&mut self, opcode: u8, reg1: Reg, reg2: Reg) {
        // opcode
        self.code.push(opcode);
        // reg1 and reg2
        let reg1_reg2 = (reg1 as u8) << 4 | reg2 as u8;
        self.code.push(reg1_reg2);
    }

    /// opcode | reg1 | reg2 | imm16
    /// 8b     | 4b   | 4b   | 16b   } 32b
    fn write_reg_reg_imm16(&mut self, opcode: u8, reg1: Reg, reg2: Reg, imm16: u16) {
        self.write_reg_reg(opcode, reg1, reg2);
        // offset
        write_half(&mut self.code, imm16);
    }

    /// Write the `jze` inst
    pub fn write_jze(&mut self, rs2: Reg, offset: u16, rs1: Reg) {
        self.write_reg_reg_imm16(Opcode::JZE_OP, rs2, rs1, offset);
    }

    /// Write the `beq` inst
    pub fn write_beq(&mut self, rs1: Reg, rs2: Reg, offset: u16) {
        self.write_reg_reg_imm16(Opcode::BEQ_OP, rs1, rs2, offset);
    }

    /// Write the `bne` inst
    pub fn write_bne(&mut self, rs1: Reg, rs2: Reg, offset: u16) {
        self.write_reg_reg_imm16(Opcode::BNE_OP, rs1, rs2, offset);
    }

    /// Write the `blt` inst
    pub fn write_blt(&mut self, rs1: Reg, rs2: Reg, offset: u16) {
        self.write_reg_reg_imm16(Opcode::BLT_OP, rs1, rs2, offset);
    }

    /// Write the `bge` inst
    pub fn write_bge(&mut self, rs1: Reg, rs2: Reg, offset: u16) {
        self.write_reg_reg_imm16(Opcode::BGE_OP, rs1, rs2, offset);
    }

    /// Write the `ld.b` inst
    pub fn write_ld_b(&mut self, rd: Reg, offset: u16, rs: Reg) {
        self.write_reg_reg_imm16(Opcode::LD_B_OP, rd, rs, offset);
    }

    /// Write the `st.b` inst
    pub fn write_st_b(&mut self, rs2: Reg, offset: u16, rs1: Reg) {
        self.write_reg_reg_imm16(Opcode::ST_B_OP, rs2, rs1, offset);
    }

    /// Write the `st.h` inst
    pub fn write_st_h(&mut self, rs2: Reg, offset: u16, rs1: Reg) {
        self.write_reg_reg_imm16(Opcode::ST_H_OP, rs2, rs1, offset);
    }

    /// Write the `st.w` inst
    pub fn write_st_w(&mut self, rs2: Reg, offset: u16, rs1: Reg) {
        self.write_reg_reg_imm16(Opcode::ST_W_OP, rs2, rs1, offset);
    }

    /// Write the `st.d` inst
    pub fn write_st_d(&mut self, rs2: Reg, offset: u16, rs1: Reg) {
        self.write_reg_reg_imm16(Opcode::ST_D_OP, rs2, rs1, offset);
    }

    /// Write the `li.b` inst
    pub fn write_li_b(&mut self, rd: Reg, imm8: u8, rs: Reg) {
        self.write_reg_reg(Opcode::LI_B_OP, rd, rs);
        // imm8
        self.code.push(imm8);
    }

    /// Write the `li.h` inst
    pub fn write_li_h(&mut self, rd: Reg, imm16: u16, rs: Reg) {
        self.write_reg_reg_imm16(Opcode::LI_H_OP, rd, rs, imm16);
    }

    /// Write the `li.w` inst
    pub fn write_li_w(&mut self, rd: Reg, imm32: u32, rs: Reg) {
        self.write_reg_reg(Opcode::LI_W_OP, rd, rs);

        // imm32
        write_word(&mut self.code, imm32);
    }

    /// Write the `li.d` inst
    pub fn write_li_d(&mut self, rd: Reg, imm64: u64, rs: Reg) {
        self.write_reg_reg(Opcode::LI_D_OP, rd, rs);

        // imm64
        write_dword(&mut self.code, imm64);
    }

    /// Write the `mov` inst
    pub fn write_mov(&mut self, rd: Reg, rs: Reg) {
        self.write_reg_reg(Opcode::MOV_OP, rd, rs);
    }

    /// Write the `push` inst
    pub fn write_push(&mut self, rs: Reg) {
        // opcode
        self.code.push(Opcode::PUSH_OP);
        // rs
        self.code.push(rs as u8);
    }

    /// Write the `pop` inst
    pub fn write_pop(&mut self, rd: Reg) {
        // opcode
        self.code.push(Opcode::POP_OP);
        // rs
        self.code.push(rd as u8);
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
        let opcode = self.code[offset];

        match Opcode::from_integer(opcode).unwrap() {
            Opcode::Add => self.dissassemble_arithmetic(offset, Opcode::ADD),
            Opcode::Sub => self.dissassemble_arithmetic(offset, Opcode::SUB),
            Opcode::Mul => self.dissassemble_arithmetic(offset, Opcode::MUL),
            Opcode::Div => self.dissassemble_arithmetic(offset, Opcode::DIV),
            Opcode::Rem => self.dissassemble_arithmetic(offset, Opcode::REM),
            Opcode::Clt => self.dissassemble_arithmetic(offset, Opcode::CLT),
            Opcode::Cge => self.dissassemble_arithmetic(offset, Opcode::CGE),
            Opcode::Ceq => self.dissassemble_arithmetic(offset, Opcode::CEQ),
            Opcode::Cne => self.dissassemble_arithmetic(offset, Opcode::CNE),
            Opcode::And => self.dissassemble_arithmetic(offset, Opcode::AND),
            Opcode::Or => self.dissassemble_arithmetic(offset, Opcode::OR),
            Opcode::Xor => self.dissassemble_arithmetic(offset, Opcode::XOR),
            Opcode::Call => {
                let imm = read_word(&self.code, offset + 1);
                // TODO: be able to retrieve what is the function name at this addr
                println!("call 0x{imm:08X}");
                offset + 5
            }
            Opcode::Ret => {
                println!("ret");
                offset + 1
            }
            Opcode::Jze => self.dissassemble_reg_imm16_reg(offset, Opcode::JZE),
            Opcode::Beq => self.dissassemble_reg_reg_imm16(offset, Opcode::BEQ),
            Opcode::Bne => self.dissassemble_reg_reg_imm16(offset, Opcode::BNE),
            Opcode::Blt => self.dissassemble_reg_reg_imm16(offset, Opcode::BLT),
            Opcode::Bge => self.dissassemble_reg_reg_imm16(offset, Opcode::BGE),
            Opcode::LdB => self.dissassemble_reg_imm16_reg(offset, Opcode::LD_B),
            Opcode::LdH => self.dissassemble_reg_imm16_reg(offset, Opcode::LD_H),
            Opcode::LdW => self.dissassemble_reg_imm16_reg(offset, Opcode::LD_W),
            Opcode::LdD => self.dissassemble_reg_imm16_reg(offset, Opcode::LD_D),
            Opcode::StB => self.dissassemble_reg_imm16_reg(offset, Opcode::ST_B),
            Opcode::StH => self.dissassemble_reg_imm16_reg(offset, Opcode::ST_H),
            Opcode::StW => self.dissassemble_reg_imm16_reg(offset, Opcode::ST_W),
            Opcode::StD => self.dissassemble_reg_imm16_reg(offset, Opcode::ST_D),
            Opcode::LiB => {
                let rd_rs = self.code[offset + 1];
                let imm8 = self.code[offset + 2];

                let rs = Reg::from_integer(rd_rs & 0b1111).unwrap();
                let rd = Reg::from_integer((rd_rs & 0b1111_0000) >> 4).unwrap();

                print!("li.b {rd}, 0x{imm8:02X}");
                if rs != Reg::zr {
                    print!("({rs})");
                }
                println!();

                offset + 3
            }
            Opcode::LiH => self.dissassemble_reg_imm16_reg(offset, Opcode::LI_H),
            Opcode::LiW => {
                let rd_rs = self.code[offset + 1];
                let imm32 = read_word(&self.code, offset + 2);

                let rs = Reg::from_integer(rd_rs & 0b1111).unwrap();
                let rd = Reg::from_integer((rd_rs & 0b1111_0000) >> 4).unwrap();

                print!("li.w {rd}, 0x{imm32:X}");
                if rs != Reg::zr {
                    print!("({rs})");
                }
                println!();

                offset + 6
            }
            Opcode::LiD => {
                let rd_rs = self.code[offset + 1];
                let imm64 = read_dword(&self.code, offset + 2);

                let rs = Reg::from_integer(rd_rs & 0b1111).unwrap();
                let rd = Reg::from_integer((rd_rs & 0b1111_0000) >> 4).unwrap();

                print!("li.d {rd}, 0x{imm64:X}");
                if rs != Reg::zr {
                    print!("({rs})");
                }
                println!();

                offset + 10
            }
            Opcode::Mov => {
                let rd_rs = self.code[offset + 1];

                let rs = Reg::from_integer(rd_rs & 0b1111).unwrap();
                let rd = Reg::from_integer((rd_rs & 0b1111_0000) >> 4).unwrap();

                println!("mov {rd}, {rs}");

                offset + 2
            }
            Opcode::Push => self.dissassemble_reg(offset, Opcode::PUSH),
            Opcode::Pop => self.dissassemble_reg(offset, Opcode::POP),
        }
    }

    fn dissassemble_arithmetic(&self, offset: usize, name: &str) -> usize {
        let funct_rd = self.code[offset + 1];
        let rs1_rs2 = self.code[offset + 2];
        let funct = AFunct::from_integer((funct_rd & 0b1111_0000) >> 4).unwrap();
        let rd = Reg::from_integer(funct_rd & 0b1111).unwrap();
        let rs1 = Reg::from_integer((rs1_rs2 & 0b1111_0000) >> 4).unwrap();
        let rs2 = Reg::from_integer(rs1_rs2 & 0b1111).unwrap();
        print!("{name}");
        if funct != AFunct::X {
            print!(".{funct}");
        }
        println!(" {rd}, {rs1}, {rs2}");
        offset + 3
    }

    /// dissassemble an instruction of the format:
    ///
    /// inst reg2, imm16(reg1)
    fn dissassemble_reg_imm16_reg(&self, offset: usize, name: &str) -> usize {
        let reg2_reg1 = self.code[offset + 1];
        let imm16 = read_half(&self.code, offset + 2);

        let reg1 = Reg::from_integer(reg2_reg1 & 0b1111).unwrap();
        let reg2 = Reg::from_integer((reg2_reg1 & 0b1111_0000) >> 4).unwrap();

        print!("{name} {reg2}, 0x{imm16:X}");
        if reg1 != Reg::zr {
            print!("({reg1})");
        }
        println!();

        offset + 4
    }

    /// dissassemble an instruction of the format:
    ///
    /// inst reg1, reg2, imm16
    fn dissassemble_reg_reg_imm16(&self, offset: usize, name: &str) -> usize {
        let reg2_reg1 = self.code[offset + 1];
        let imm16 = read_half(&self.code, offset + 2);

        let reg1 = Reg::from_integer(reg2_reg1 & 0b1111).unwrap();
        let reg2 = Reg::from_integer((reg2_reg1 & 0b1111_0000) >> 4).unwrap();

        println!("{name} {reg1}, {reg2}, 0x{imm16:X}");
        offset + 4
    }

    /// dissassemble an instruction of the format:
    ///
    /// inst reg
    fn dissassemble_reg(&self, offset: usize, name: &str) -> usize {
        let zero_reg = self.code[offset + 1];

        let reg = Reg::from_integer(zero_reg & 0b1111).unwrap();

        println!("{name} {reg}");
        offset + 4
    }
}
