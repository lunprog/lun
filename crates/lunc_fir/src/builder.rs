//! FIR Building Helpers.

use super::*;

/// Helping structure to build one function of FIR.
#[derive(Debug)]
pub struct FundefBuilder<'fir> {
    /// function being built in
    fun: &'fir mut FunDef,
    /// current basic block, the last inserted in the current function
    current_bb: Option<&'fir mut BasicBlock>,
    /// last basic block label of the current function
    last_bb_label: u32,
}

impl<'fir> FundefBuilder<'fir> {
    /// Create a new fir unit builder
    pub fn new(fun: &'fir mut FunDef) -> FundefBuilder<'fir> {
        FundefBuilder {
            fun,
            current_bb: None,
            last_bb_label: 0,
        }
    }

    /// Create a new basic block in the current function
    pub fn create_bb(&'fir mut self) -> BbLabel {
        let label = BbLabel::new(self.last_bb_label);

        let bb = BasicBlock::new(label);

        self.fun.bbs.push(bb);

        self.current_bb = Some(self.fun.bbs.last_mut().unwrap());

        label
    }

    // /// Returns the last basic block appended to the bbs.
    // pub fn bb(&mut self) -> &mut BasicBlock {}

    /// Returns an instruction builder that builds instruction in the current
    /// block of the current function
    pub fn inst(&mut self) {}
}

/// A trait for types able to build [instructions] and [terminators].
///
/// [instructions]: crate::Inst
/// [terminators]: crate::Terminator
pub trait InstBuilder {
    /// Build an instruction given the [`Inst`].
    ///
    /// # Note
    ///
    /// If a call to this method is done after building a terminator
    /// instruction, this method must do nothing.
    fn build_inst(&mut self, inst: Inst);

    /// Build a terminator given the [`Terminator`].
    fn build_terminator(&mut self, terminator: Terminator);

    // the instructions

    /// Build a [`Call`] instruction.
    ///
    /// # Inputs
    ///
    /// - `res`: the register in which the return of the call gets put
    /// - `ty`: the type of the returned value
    /// - `fnptr`: the callee
    /// - `args`: the arguments passed to the callee
    ///
    /// [`Call`]: crate::Inst::Call
    fn call(&mut self, res: Reg, ty: FcType, fnptr: Arg, args: impl IntoIterator<Item = Arg>) {
        self.build_inst(Inst::Call {
            res,
            ty,
            fnptr,
            args: args.into_iter().collect(),
        });
    }

    /// Build an [`Add`] instruction.
    ///
    /// # Inputs
    ///
    /// - `res`: the register in which the result gets put
    /// - `ty`: the type of the result and of the inputs
    /// - `lhs`: the left-hand side of the operation
    /// - `rhs`: the right-hand side of the operation
    ///
    /// [`Add`]: crate::Inst::Add
    fn add(&mut self, res: Reg, ty: FcType, lhs: Arg, rhs: Arg) {
        self.build_inst(Inst::Add { res, ty, lhs, rhs });
    }

    /// Build an [`Fadd`] instruction.
    ///
    /// # Inputs
    ///
    /// - `res`: the register in which the result gets put
    /// - `ty`: the type of the result and of the inputs
    /// - `lhs`: the left-hand side of the operation
    /// - `rhs`: the right-hand side of the operation
    ///
    /// [`Fadd`]: crate::Inst::Fadd
    fn fadd(&mut self, res: Reg, ty: FcType, lhs: Arg, rhs: Arg) {
        self.build_inst(Inst::Fadd { res, ty, lhs, rhs });
    }

    /// Build an [`Sub`] instruction.
    ///
    /// # Inputs
    ///
    /// - `res`: the register in which the result gets put
    /// - `ty`: the type of the result and of the inputs
    /// - `lhs`: the left-hand side of the operation
    /// - `rhs`: the right-hand side of the operation
    ///
    /// [`Sub`]: crate::Inst::Sub
    fn sub(&mut self, res: Reg, ty: FcType, lhs: Arg, rhs: Arg) {
        self.build_inst(Inst::Sub { res, ty, lhs, rhs });
    }

    /// Build an [`Fsub`] instruction.
    ///
    /// # Inputs
    ///
    /// - `res`: the register in which the result gets put
    /// - `ty`: the type of the result and of the inputs
    /// - `lhs`: the left-hand side of the operation
    /// - `rhs`: the right-hand side of the operation
    ///
    /// [`Fsub`]: crate::Inst::Fsub
    fn fsub(&mut self, res: Reg, ty: FcType, lhs: Arg, rhs: Arg) {
        self.build_inst(Inst::Fsub { res, ty, lhs, rhs });
    }

    /// Build an [`Mul`] instruction.
    ///
    /// # Inputs
    ///
    /// - `res`: the register in which the result gets put
    /// - `ty`: the type of the result and of the inputs
    /// - `lhs`: the left-hand side of the operation
    /// - `rhs`: the right-hand side of the operation
    ///
    /// [`Mul`]: crate::Inst::Mul
    fn mul(&mut self, res: Reg, ty: FcType, lhs: Arg, rhs: Arg) {
        self.build_inst(Inst::Mul { res, ty, lhs, rhs });
    }

    /// Build an [`Fmul`] instruction.
    ///
    /// # Inputs
    ///
    /// - `res`: the register in which the result gets put
    /// - `ty`: the type of the result and of the inputs
    /// - `lhs`: the left-hand side of the operation
    /// - `rhs`: the right-hand side of the operation
    ///
    /// [`Fmul`]: crate::Inst::Fmul
    fn fmul(&mut self, res: Reg, ty: FcType, lhs: Arg, rhs: Arg) {
        self.build_inst(Inst::Fmul { res, ty, lhs, rhs });
    }

    /// Build an [`Udiv`] instruction.
    ///
    /// # Inputs
    ///
    /// - `res`: the register in which the result gets put
    /// - `ty`: the type of the result and of the inputs
    /// - `lhs`: the left-hand side of the operation
    /// - `rhs`: the right-hand side of the operation
    ///
    /// [`Udiv`]: crate::Inst::Udiv
    fn udiv(&mut self, res: Reg, ty: FcType, lhs: Arg, rhs: Arg) {
        self.build_inst(Inst::Udiv { res, ty, lhs, rhs });
    }

    /// Build an [`Sdiv`] instruction.
    ///
    /// # Inputs
    ///
    /// - `res`: the register in which the result gets put
    /// - `ty`: the type of the result and of the inputs
    /// - `lhs`: the left-hand side of the operation
    /// - `rhs`: the right-hand side of the operation
    ///
    /// [`Sdiv`]: crate::Inst::Sdiv
    fn sdiv(&mut self, res: Reg, ty: FcType, lhs: Arg, rhs: Arg) {
        self.build_inst(Inst::Sdiv { res, ty, lhs, rhs });
    }

    /// Build an [`Fdiv`] instruction.
    ///
    /// # Inputs
    ///
    /// - `res`: the register in which the result gets put
    /// - `ty`: the type of the result and of the inputs
    /// - `lhs`: the left-hand side of the operation
    /// - `rhs`: the right-hand side of the operation
    ///
    /// [`Fdiv`]: crate::Inst::Fdiv
    fn fdiv(&mut self, res: Reg, ty: FcType, lhs: Arg, rhs: Arg) {
        self.build_inst(Inst::Fdiv { res, ty, lhs, rhs });
    }

    /// Build an [`Urem`] instruction.
    ///
    /// # Inputs
    ///
    /// - `res`: the register in which the result gets put
    /// - `ty`: the type of the result and of the inputs
    /// - `lhs`: the left-hand side of the operation
    /// - `rhs`: the right-hand side of the operation
    ///
    /// [`Urem`]: crate::Inst::Urem
    fn urem(&mut self, res: Reg, ty: FcType, lhs: Arg, rhs: Arg) {
        self.build_inst(Inst::Urem { res, ty, lhs, rhs });
    }

    /// Build an [`Srem`] instruction.
    ///
    /// # Inputs
    ///
    /// - `res`: the register in which the result gets put
    /// - `ty`: the type of the result and of the inputs
    /// - `lhs`: the left-hand side of the operation
    /// - `rhs`: the right-hand side of the operation
    ///
    /// [`Srem`]: crate::Inst::Srem
    fn srem(&mut self, res: Reg, ty: FcType, lhs: Arg, rhs: Arg) {
        self.build_inst(Inst::Srem { res, ty, lhs, rhs });
    }

    /// Build an [`Frem`] instruction.
    ///
    /// # Inputs
    ///
    /// - `res`: the register in which the result gets put
    /// - `ty`: the type of the result and of the inputs
    /// - `lhs`: the left-hand side of the operation
    /// - `rhs`: the right-hand side of the operation
    ///
    /// [`Frem`]: crate::Inst::Frem
    fn frem(&mut self, res: Reg, ty: FcType, lhs: Arg, rhs: Arg) {
        self.build_inst(Inst::Frem { res, ty, lhs, rhs });
    }

    /// Build an [`And`] instruction.
    ///
    /// # Inputs
    ///
    /// - `res`: the register in which the result gets put
    /// - `ty`: the type of the result and of the inputs
    /// - `lhs`: the left-hand side of the operation
    /// - `rhs`: the right-hand side of the operation
    ///
    /// [`And`]: crate::Inst::And
    fn and(&mut self, res: Reg, ty: FcType, lhs: Arg, rhs: Arg) {
        self.build_inst(Inst::And { res, ty, lhs, rhs });
    }

    /// Build an [`Xor`] instruction.
    ///
    /// # Inputs
    ///
    /// - `res`: the register in which the result gets put
    /// - `ty`: the type of the result and of the inputs
    /// - `lhs`: the left-hand side of the operation
    /// - `rhs`: the right-hand side of the operation
    ///
    /// [`Xor`]: crate::Inst::Xor
    fn xor(&mut self, res: Reg, ty: FcType, lhs: Arg, rhs: Arg) {
        self.build_inst(Inst::Xor { res, ty, lhs, rhs });
    }

    /// Build an [`Or`] instruction.
    ///
    /// # Inputs
    ///
    /// - `res`: the register in which the result gets put
    /// - `ty`: the type of the result and of the inputs
    /// - `lhs`: the left-hand side of the operation
    /// - `rhs`: the right-hand side of the operation
    ///
    /// [`Or`]: crate::Inst::Or
    fn or(&mut self, res: Reg, ty: FcType, lhs: Arg, rhs: Arg) {
        self.build_inst(Inst::Xor { res, ty, lhs, rhs });
    }

    /// Build an [`Shr`] instruction.
    ///
    /// # Inputs
    ///
    /// - `res`: the register in which the result gets put
    /// - `ty`: the type of the result and of the inputs
    /// - `lhs`: the left-hand side of the operation
    /// - `rhs`: the right-hand side of the operation
    ///
    /// [`Shr`]: crate::Inst::Shr
    fn shr(&mut self, res: Reg, ty: FcType, lhs: Arg, rhs: Arg) {
        self.build_inst(Inst::Shr { res, ty, lhs, rhs });
    }

    /// Build an [`Shl`] instruction.
    ///
    /// # Inputs
    ///
    /// - `res`: the register in which the result gets put
    /// - `ty`: the type of the result and of the inputs
    /// - `lhs`: the left-hand side of the operation
    /// - `rhs`: the right-hand side of the operation
    ///
    /// [`shl`]: crate::Inst::Shl
    fn shl(&mut self, res: Reg, ty: FcType, lhs: Arg, rhs: Arg) {
        self.build_inst(Inst::Shl { res, ty, lhs, rhs });
    }

    /// Build an [`Neg`] instruction.
    ///
    /// # Inputs
    ///
    /// - `res`: the register in which the result gets put
    /// - `ty`: the type of the result and of the inputs
    /// - `op`: the operand of the operation
    ///
    /// [`Neg`]: crate::Inst::Neg
    fn neg(&mut self, res: Reg, ty: FcType, op: Arg) {
        self.build_inst(Inst::Neg { res, ty, op });
    }

    /// Build an [`Fneg`] instruction.
    ///
    /// # Inputs
    ///
    /// - `res`: the register in which the result gets put
    /// - `ty`: the type of the result and of the inputs
    /// - `op`: the operand of the operation
    ///
    /// [`Fneg`]: crate::Inst::Fneg
    fn fneg(&mut self, res: Reg, ty: FcType, op: Arg) {
        self.build_inst(Inst::Fneg { res, ty, op });
    }

    /// Build an [`Icmp`] instruction.
    ///
    /// # Inputs
    ///
    /// - `res`: the register in which the result gets put
    /// - `cc`: [comparison code] performed on `lhs` and `rhs`
    /// - `lhs`: left-hand side of the comparison
    /// - `rhs`: right-hand side of the comparison
    ///
    /// [`Icmp`]: crate::Inst::Icmp
    /// [comparison code]: crate::IntCC
    fn icmp(&mut self, res: Reg, cc: IntCC, lhs: Arg, rhs: Arg) {
        self.build_inst(Inst::Icmp { res, cc, lhs, rhs });
    }

    /// Build a [`Salloc`] instruction.
    ///
    /// # Inputs
    ///
    /// - `res`: the register in which the result gets put
    /// - `ty`: the type of the allocated memory
    /// - `num_elems`: optional number of elements to allocate
    /// - `alignment`: the alignment of the allocation
    ///
    /// [`Salloc`]: crate::Inst::Salloc
    fn salloc(
        &mut self,
        res: Reg,
        ty: FcType,
        num_elems: impl Into<Option<u32>>,
        alignment: Alignment,
    ) {
        self.build_inst(Inst::Salloc {
            res,
            ty,
            num_elems: num_elems.into(),
            alignment,
        });
    }

    /// Build a [`Load`] instruction.
    ///
    /// # Inputs
    ///
    /// - `res`: the register in which the result gets put
    /// - `ty`: the type of the allocated memory
    /// - `pointer`: the pointer from which the memory gets load into the register
    ///
    /// [`Load`]: crate::Inst::Load
    fn load(&mut self, res: Reg, ty: FcType, pointer: Arg) {
        self.build_inst(Inst::Load { res, ty, pointer });
    }

    /// Build a [`Store`] instruction.
    ///
    /// # Inputs
    ///
    /// - `ty`: the type of `val`
    /// - `val`: the value written to memory
    /// - `pointer`: the pointer where we will write the `val`
    ///
    /// [`Store`]: crate::Inst::Store
    fn store(&mut self, ty: FcType, val: Arg, pointer: Arg) {
        self.build_inst(Inst::Store { ty, val, pointer });
    }

    // the terminators

    /// Build a [`Br`] terminator.
    ///
    /// # Inputs
    ///
    /// - `cond`: the condition of the branch
    /// - `true_br`: the branch taken when `cond` evaluates to `true`
    /// - `false_br`: the branch taken when `cond` evaluates to `false`
    ///
    /// # Note
    ///
    /// Because this is a terminator, this terminator cannot have successors,
    /// so subsequent call to one of the [`InstBuilder`] method will have no
    /// effect.
    ///
    /// [`Br`]: crate::Terminator::Br
    fn br(&mut self, cond: Arg, true_br: BbLabel, false_br: BbLabel) {
        self.build_terminator(Terminator::Br {
            cond,
            true_br,
            false_br,
        });
    }

    /// Build a [`BrIcmp`] terminator.
    ///
    /// # Inputs
    ///
    /// - `cc`: [comparison code] performed on `lhs` and `rhs`
    /// - `lhs`: left-hand side of the condition
    /// - `rhs`: right-hand side of the condition
    /// - `true_br`: the branch taken when the condition evaluates to `true`
    /// - `false_br`: the branch taken when the condition evaluates to `false`
    ///
    /// # Note
    ///
    /// Because this is a terminator, this terminator cannot have successors,
    /// so subsequent call to one of the [`InstBuilder`] method will have no
    /// effect.
    ///
    /// [`BrIcmp`]: crate::Terminator::BrIcmp
    /// [comparison code]: crate::IntCC
    fn br_icmp(&mut self, cc: IntCC, lhs: Arg, rhs: Arg, true_br: BbLabel, false_br: BbLabel) {
        self.build_terminator(Terminator::BrIcmp {
            cc,
            lhs,
            rhs,
            true_br,
            false_br,
        });
    }

    /// Build a [`Jump`] terminator.
    ///
    /// # Input
    ///
    /// - `dest`: the destination block
    ///
    /// # Note
    ///
    /// Because this is a terminator, this terminator cannot have successors,
    /// so subsequent call to one of the [`InstBuilder`] method will have no
    /// effect.
    ///
    /// [`Jump`]: crate::Terminator::Jump
    fn jump(&mut self, dest: BbLabel) {
        self.build_terminator(Terminator::Jump { dest });
    }

    /// Build a [`Ret`] terminator.
    ///
    /// # Input
    ///
    /// - `ty`: the type of the returned value
    /// - `val`: the optional value returned
    ///
    /// # Note
    ///
    /// Because this is a terminator, this terminator cannot have successors,
    /// so subsequent call to one of the [`InstBuilder`] method will have no
    /// effect.
    ///
    /// [`Ret`]: crate::Terminator::Ret
    fn ret(&mut self, ty: FcType, val: Option<Arg>) {
        self.build_terminator(Terminator::Ret { ty, val });
    }
}
