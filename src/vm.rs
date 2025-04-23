//! The virtual machine for l2's bytecode.

use crate::{
    blob::{Blob, OpCode},
    read_dword, read_word,
};

use std::mem;

/// The stack of the VM
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct Stack {
    pub stack: Vec<u8>,
    /// stack pointer, always points at the element just past the element
    /// containing the top value
    pub sp: usize,
}

impl Stack {
    // TODO: maybe adjust it later.
    /// Default capacity of the stack, it can grow as the program runs.
    pub const DEFAULT_CAPACITY: usize = 0x4000;
    /// The default minimum amount of bytes we allocate when the stack isn't big enough.
    pub const DEFAULT_GROWTH: usize = 0x800;

    pub fn new() -> Stack {
        Stack {
            stack: vec![0; Stack::DEFAULT_CAPACITY],
            sp: 0,
        }
    }

    pub fn push(&mut self, val: &[u8]) {
        if val.len() + self.sp > self.stack.len() {
            self.grow(Stack::DEFAULT_GROWTH);
        }
        self.stack
            .splice(self.sp..self.sp + val.len(), val.iter().cloned());
        self.sp += val.len();
    }

    pub fn grow(&mut self, additional: usize) {
        self.stack.reserve(additional);

        // we don't do it with `additional` because calling reserve might
        // allocate more than what we wanted.
        let added = self.stack.capacity() - self.stack.len();

        for _ in 0..added {
            self.stack.push(0);
        }
    }

    pub fn pop(&mut self, size: usize) -> &[u8] {
        let bytes = &self.stack[self.sp - size..self.sp];
        self.sp -= size;
        bytes
    }

    pub fn pop_qword(&mut self) -> u64 {
        let bytes = self.pop(size_of::<u64>()).try_into().unwrap();
        u64::from_le_bytes(bytes)
    }

    pub fn push_qword(&mut self, int: u64) {
        let bytes = int.to_le_bytes();
        self.push(&bytes);
    }

    pub fn pop_integer(&mut self) -> i64 {
        // SAFETY: no worries, it's safe just some integer transmutes ;)
        unsafe { mem::transmute(self.pop_qword()) }
    }

    pub fn push_integer(&mut self, int: i64) {
        unsafe {
            // SAFETY: no worries, it's safe just some integer transmutes ;)
            self.push_qword(mem::transmute(int));
        }
    }
}

macro_rules! binary_op {
    ($self:expr, $op:tt) => ({
        let b = $self.stack.pop_integer();
        let a = $self.stack.pop_integer();

        $self.stack.push_integer(a $op b);
    });
}

/// The Virtual Machine of L2.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct VM {
    /// blob of code, we will execute
    blob: Blob,
    /// instruction pointer, always points to the instruction that is about to
    /// be executed
    ip: usize,
    /// the stack
    stack: Stack,
}

impl VM {
    pub fn new(blob: Blob) -> VM {
        VM {
            blob,
            ip: 0,
            stack: Stack::new(),
        }
    }

    fn read_byte(&mut self) -> u8 {
        let byte = self.blob.code[self.ip];
        self.ip += 1;
        byte
    }

    fn read_word(&mut self) -> u16 {
        let word = read_word(&self.blob.code, self.ip);
        self.ip += 2;
        word
    }

    fn read_dword(&mut self) -> u32 {
        let dword = read_dword(&self.blob.code, self.ip);
        self.ip += 4;
        dword
    }

    pub fn run(&mut self) -> u64 {
        loop {
            // TODO: handle runtime errors, remove the unwrap
            // maybe handle them like in real ISA, like traps/interrupts that
            // can recover idk from the code.
            let opcode = self.read_byte();
            // Dispatch the opcode
            match OpCode::from_u8(opcode).unwrap() {
                OpCode::Ret => break,
                OpCode::Const => {
                    let offset = self.read_dword();
                    let size = self.read_word();

                    let val = self.blob.dpool.read_many(offset as usize, size as usize);
                    self.stack.push(val);
                }
                OpCode::Neg => {
                    let int = self.stack.pop_integer();
                    self.stack.push_integer(-int);
                }
                OpCode::Add => binary_op!(self, +),
                OpCode::Sub => binary_op!(self, -),
                OpCode::Mul => binary_op!(self, *),
                OpCode::Div => binary_op!(self, /),
            }
        }

        self.stack.pop_qword()
    }
}
