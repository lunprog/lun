//! The virtual machine for lun's bytecode.

use std::{
    fmt::Debug,
    ops::{Index, IndexMut},
};

use bytemuck::Contiguous;
use lun_bc::{AFunct, BcBlob, Opcode, Reg};

/// A double word.
pub type DWord = u64;

#[derive(Debug, Clone)]
pub struct Vm {
    /// general purpose registers
    x: Registers,
    /// register instruction pointer
    pc: DWord,
    /// program_end address
    program_end: DWord,
    /// stack bottom address
    stack_bottom: DWord,
    /// canary end address
    canary_end: DWord,
    /// the canary
    program: BcBlob,
    /// the stack
    stack: Vec<u8>,
    /// is execution finished
    done: bool,
}

impl Vm {
    /// The size of the canary, 1024 bytes.
    pub const CANARY_SIZE: DWord = 1024;

    /// Address where the special memory region is ending
    pub const SPECIAL_END: DWord = 255;

    /// Address where the program is loaded.
    pub const PROGRAM_START: DWord = Vm::SPECIAL_END + 1;

    /// Default stack size.
    ///
    /// Note: this default may change at any time between versions.
    pub const BASE_STACK: DWord = 0x8000;

    pub fn new(stack_size: DWord, program: BcBlob) -> Vm {
        let program_end = Vm::PROGRAM_START + program.code.len() as DWord;
        let stack_top = program_end + 1;
        let stack_bottom = stack_top + stack_size;
        let canary_start = stack_bottom + 1;
        let canary_end = canary_start + Vm::CANARY_SIZE;

        Vm {
            x: Registers([0; 16]),
            pc: Vm::PROGRAM_START,
            program_end,
            stack_bottom,
            canary_end,
            program,
            stack: vec![0; stack_size as usize],
            done: false,
        }
    }

    pub fn debug_regs(&self) {
        println!("{:#?}", self.x);
    }

    pub fn run(&mut self) {
        while !self.done {
            let opcode = Opcode::from_integer(self.read(self.pc, Size::Byte) as u8);

            match opcode {
                Some(Opcode::Add) => {
                    let (funct, rd, rs1, rs2) = self.decode_arithmetic_inst();
                    self.pc += 3;
                    dbg!(
                        funct,
                        Reg::from_integer(rd),
                        Reg::from_integer(rs1),
                        Reg::from_integer(rs2)
                    );
                }
                Some(_) => todo!(),
                None => panic!("invalid instruction exception"), // TODO: make excetpions.
            }
            break;
        }
    }

    fn decode_arithmetic_inst(&self) -> (AFunct, u8, u8, u8) {
        let funct_rd = self.read(self.pc + 1, Size::Byte) as u8;
        let rs1_rs2 = self.read(self.pc + 2, Size::Byte) as u8;

        let funct = AFunct::from_integer(funct_rd >> 4).unwrap();
        let rd = funct_rd & 0b1111;
        let rs1 = rs1_rs2 >> 4;
        let rs2 = rs1_rs2 & 0b1111;

        (funct, rd, rs1, rs2)
    }

    #[inline(always)]
    pub const fn stack_top(&self) -> DWord {
        self.program_end + 1
    }

    #[inline(always)]
    pub const fn canary_start(&self) -> DWord {
        self.stack_bottom + 1
    }

    #[inline(always)]
    pub const fn heap_base(&self) -> DWord {
        self.canary_end + 1
    }

    pub fn read(&self, addr: DWord, size: Size) -> DWord {
        let usize = size as usize;
        if addr % size as u64 != 0 {
            // TODO: throw an interrupt
            panic!("non-aligned address")
        }

        let val = if (0..=255).contains(&addr) {
            // TODO: throw interrupts
            panic!("cannot read special region.")
        } else if (Self::PROGRAM_START..=self.program_end).contains(&addr) {
            let daddr = addr as usize - Vm::PROGRAM_START as usize;
            &self.program.code[daddr..(daddr + usize)]
        } else if (self.stack_top()..self.stack_bottom).contains(&addr) {
            let daddr = addr as usize - self.stack_top() as usize;
            &self.stack[daddr..(daddr + usize)]
        } else {
            // TODO: throw interrupts
            panic!("unknown address")
        };

        match size {
            Size::Byte => *bytemuck::from_bytes::<u8>(val) as DWord,
            Size::Half => *bytemuck::from_bytes::<u16>(val) as DWord,
            Size::Word => *bytemuck::from_bytes::<u32>(val) as DWord,
            Size::Double => *bytemuck::from_bytes::<u64>(val) as DWord,
        }
    }

    pub fn write(&mut self, addr: DWord, size: Size, value: DWord) {
        let usize = size as usize;
        if addr % size as u64 != 0 {
            // TODO: throw an interrupt
            panic!("non-aligned address");
        }

        // Get mutable slice to write into
        let dest = if (0..=255).contains(&addr) {
            // TODO: throw interrupt
            panic!("cannot write to special region.");
        } else if (Self::PROGRAM_START..=self.program_end).contains(&addr) {
            // Program region is read-only
            // TODO: throw interrupt
            panic!("cannot write to program region.");
        } else if (self.stack_top()..self.stack_bottom).contains(&addr) {
            let daddr = addr as usize - self.stack_top() as usize;
            &mut self.stack[daddr..(daddr + usize)]
        } else {
            // TODO: throw interrupt
            panic!("unknown address");
        };

        match size {
            Size::Byte => {
                let val = value as u8;
                let bytes = bytemuck::bytes_of(&val);
                dest.copy_from_slice(bytes);
            }
            Size::Half => {
                let val = value as u16;
                let bytes = bytemuck::bytes_of(&val);
                dest.copy_from_slice(bytes);
            }
            Size::Word => {
                let val = value as u32;
                let bytes = bytemuck::bytes_of(&val);
                dest.copy_from_slice(bytes);
            }
            Size::Double => {
                let val = value;
                let bytes = bytemuck::bytes_of(&val);
                dest.copy_from_slice(bytes);
            }
        }
    }
}

#[derive(Clone)]
pub struct Registers([DWord; 16]);

impl Debug for Registers {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Registers")
            .field("zr", &self.0[0])
            .field("a0", &self.0[1])
            .field("a1", &self.0[2])
            .field("a2", &self.0[3])
            .field("a3", &self.0[4])
            .field("a4", &self.0[5])
            .field("t0", &self.0[6])
            .field("t1", &self.0[7])
            .field("t2", &self.0[8])
            .field("t3", &self.0[9])
            .field("s0", &self.0[10])
            .field("s1", &self.0[11])
            .field("s2", &self.0[12])
            .field("s3", &self.0[13])
            .field("fp", &self.0[14])
            .field("sp", &self.0[15])
            .finish()
    }
}

impl Index<u8> for Registers {
    type Output = DWord;

    fn index(&self, index: u8) -> &Self::Output {
        debug_assert!((0..16).contains(&index), "There is only 16 registers");

        if index == 0 {
            &0
        } else {
            &self.0[index as usize]
        }
    }
}

impl IndexMut<u8> for Registers {
    fn index_mut(&mut self, index: u8) -> &mut Self::Output {
        debug_assert!((0..16).contains(&index), "There is only 16 registers");
        // NOTE: here we are fine because, we check that index is 0..16 and if
        // you write something to rze, you will not be able to read it using the
        // index expr.
        self.0.index_mut(index as usize)
    }
}

#[repr(u8)]
#[derive(Debug, Clone, Copy)]
pub enum Size {
    Byte = 1,
    Half = 2,
    Word = 4,
    Double = 8,
}
