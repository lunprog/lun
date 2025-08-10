//! FIR Building Helpers.

use std::collections::HashMap;

use super::*;

/// Helping structure to build one function of FIR.
#[derive(Debug)]
pub struct FundefBuilder {
    /// function being built in
    fun: FunDef,
    /// current basic block, the last inserted in the current function
    current_bb: Option<BasicBlock>,
    /// last basic block label of the current function
    last_bb_label: u32,
    /// the current function definition instruction builder.
    current_inst_builder: Option<FundefInstBuilder>,
    /// last register count of a bb
    last_reg: HashMap<BbLabel, u32>,
}

impl FundefBuilder {
    /// Create a new fir unit builder
    pub fn new(fun: FunDef) -> FundefBuilder {
        FundefBuilder {
            fun,
            current_bb: None,
            last_bb_label: 0,
            current_inst_builder: None,
            last_reg: HashMap::new(),
        }
    }

    /// Create the entry basic block
    pub fn create_entry(&mut self) -> BasicBlock {
        let args = self.fun.inspect(|this| this.args.clone());

        self.create_bb(args)
    }

    /// Create a new basic block in the current function, and make it the
    /// current block.
    pub fn create_bb(&mut self, args: impl IntoIterator<Item = FcType>) -> BasicBlock {
        // creating the label
        let label = BbLabel::new(self.last_bb_label);
        self.last_bb_label += 1;

        let args: Vec<FcType> = args.into_iter().collect();
        let args_len = args.len();

        // creating the block
        let bb = BasicBlock::new(label, args);

        // insert the block in the function
        self.fun.inspect_once(|this| {
            this.bbs.push(bb.clone());
        });

        // set the current block
        self.current_bb = Some(self.fun.last_bb().expect("just inserted a new bb"));

        // set the last reg index
        self.last_reg.insert(label, args_len as u32 + 1);

        bb
    }

    /// Create a new register in the block `label`.
    pub fn reg_in(&mut self, label: BbLabel) -> Reg {
        let val = self.last_reg.get_mut(&label).unwrap();
        let reg = Reg::new(*val);

        *val += 1;

        reg
    }

    /// Create a new register in the current block
    pub fn reg(&mut self) -> Reg {
        let label = self.bblock().label();

        self.reg_in(label)
    }

    /// Returns the current basic block
    pub fn bblock(&mut self) -> BasicBlock {
        self.current_bb.as_ref().unwrap().clone()
    }

    /// Set the current block to be the one with `label`, and changes the
    /// current block of the current instruction builder if any, to the one
    /// refered to as `label`.
    pub fn switch_bb(&mut self, label: BbLabel) {
        let bb = self.fun.get_bb(label).expect("unknown label");
        self.current_bb = Some(bb.clone());

        if let Some(inst_builder) = &self.current_inst_builder {
            inst_builder.inspect_mut(|this| {
                this.bb = bb.clone();
            })
        }
    }

    /// Returns the current instruction builder or create a an instruction
    /// builder if it doesn't exist.
    pub fn inst(&mut self) -> FundefInstBuilder {
        if let Some(inst_builder) = &self.current_inst_builder {
            return inst_builder.clone();
        }

        let inst_builder = FundefInstBuilder::with_internal(InternalFundefInstBuilder {
            bb: self.current_bb.clone().unwrap(),
        });

        self.current_inst_builder = Some(inst_builder.clone());

        inst_builder
    }
}

idtype! {
    /// An instruction builder for a basic block in a function definition, created
    /// with [`inst`].
    ///
    /// [`inst`]: crate::builder::FundefBuilder::inst
    pub struct FundefInstBuilder {
        bb: BasicBlock,
    }
}

impl InstBuilder for FundefInstBuilder {
    fn build_inst(&mut self, inst: Inst) {
        self.inspect_once(|this| {
            if this.bb.is_terminated() {
                // NOTE: we do nothing the block is already terminated
                return;
            }

            this.bb.append_inst(inst);
        })
    }

    fn build_terminator(&mut self, terminator: Terminator) {
        self.inspect_once(|this| {
            if this.bb.is_terminated() {
                // NOTE: we do nothing the block is already terminated
                return;
            }

            this.bb.set_terminator(terminator);
        })
    }
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
    ///
    /// # Note
    ///
    /// If a terminator was already build in the Basic Block, then calling this
    /// function is a no-op.
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
    fn call(
        &mut self,
        res: impl Into<Reg>,
        ty: FcType,
        fnptr: Arg,
        args: impl IntoIterator<Item = Arg>,
    ) {
        self.build_inst(Inst::Call {
            res: res.into(),
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
    fn add(&mut self, res: impl Into<Reg>, ty: FcType, lhs: Arg, rhs: Arg) {
        self.build_inst(Inst::Add {
            res: res.into(),
            ty,
            lhs,
            rhs,
        });
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
    fn fadd(&mut self, res: impl Into<Reg>, ty: FcType, lhs: Arg, rhs: Arg) {
        self.build_inst(Inst::Fadd {
            res: res.into(),
            ty,
            lhs,
            rhs,
        });
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
    fn sub(&mut self, res: impl Into<Reg>, ty: FcType, lhs: Arg, rhs: Arg) {
        self.build_inst(Inst::Sub {
            res: res.into(),
            ty,
            lhs,
            rhs,
        });
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
    fn fsub(&mut self, res: impl Into<Reg>, ty: FcType, lhs: Arg, rhs: Arg) {
        self.build_inst(Inst::Fsub {
            res: res.into(),
            ty,
            lhs,
            rhs,
        });
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
    fn mul(&mut self, res: impl Into<Reg>, ty: FcType, lhs: Arg, rhs: Arg) {
        self.build_inst(Inst::Mul {
            res: res.into(),
            ty,
            lhs,
            rhs,
        });
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
    fn fmul(&mut self, res: impl Into<Reg>, ty: FcType, lhs: Arg, rhs: Arg) {
        self.build_inst(Inst::Fmul {
            res: res.into(),
            ty,
            lhs,
            rhs,
        });
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
    fn udiv(&mut self, res: impl Into<Reg>, ty: FcType, lhs: Arg, rhs: Arg) {
        self.build_inst(Inst::Udiv {
            res: res.into(),
            ty,
            lhs,
            rhs,
        });
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
    fn sdiv(&mut self, res: impl Into<Reg>, ty: FcType, lhs: Arg, rhs: Arg) {
        self.build_inst(Inst::Sdiv {
            res: res.into(),
            ty,
            lhs,
            rhs,
        });
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
    fn fdiv(&mut self, res: impl Into<Reg>, ty: FcType, lhs: Arg, rhs: Arg) {
        self.build_inst(Inst::Fdiv {
            res: res.into(),
            ty,
            lhs,
            rhs,
        });
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
    fn urem(&mut self, res: impl Into<Reg>, ty: FcType, lhs: Arg, rhs: Arg) {
        self.build_inst(Inst::Urem {
            res: res.into(),
            ty,
            lhs,
            rhs,
        });
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
    fn srem(&mut self, res: impl Into<Reg>, ty: FcType, lhs: Arg, rhs: Arg) {
        self.build_inst(Inst::Srem {
            res: res.into(),
            ty,
            lhs,
            rhs,
        });
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
    fn frem(&mut self, res: impl Into<Reg>, ty: FcType, lhs: Arg, rhs: Arg) {
        self.build_inst(Inst::Frem {
            res: res.into(),
            ty,
            lhs,
            rhs,
        });
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
    fn and(&mut self, res: impl Into<Reg>, ty: FcType, lhs: Arg, rhs: Arg) {
        self.build_inst(Inst::And {
            res: res.into(),
            ty,
            lhs,
            rhs,
        });
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
    fn xor(&mut self, res: impl Into<Reg>, ty: FcType, lhs: Arg, rhs: Arg) {
        self.build_inst(Inst::Xor {
            res: res.into(),
            ty,
            lhs,
            rhs,
        });
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
    fn or(&mut self, res: impl Into<Reg>, ty: FcType, lhs: Arg, rhs: Arg) {
        self.build_inst(Inst::Xor {
            res: res.into(),
            ty,
            lhs,
            rhs,
        });
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
    fn shr(&mut self, res: impl Into<Reg>, ty: FcType, lhs: Arg, rhs: Arg) {
        self.build_inst(Inst::Shr {
            res: res.into(),
            ty,
            lhs,
            rhs,
        });
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
    fn shl(&mut self, res: impl Into<Reg>, ty: FcType, lhs: Arg, rhs: Arg) {
        self.build_inst(Inst::Shl {
            res: res.into(),
            ty,
            lhs,
            rhs,
        });
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
    fn neg(&mut self, res: impl Into<Reg>, ty: FcType, op: Arg) {
        self.build_inst(Inst::Neg {
            res: res.into(),
            ty,
            op,
        });
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
    fn fneg(&mut self, res: impl Into<Reg>, ty: FcType, op: Arg) {
        self.build_inst(Inst::Fneg {
            res: res.into(),
            ty,
            op,
        });
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
    fn icmp(&mut self, res: impl Into<Reg>, cc: IntCC, lhs: Arg, rhs: Arg) {
        self.build_inst(Inst::Icmp {
            res: res.into(),
            cc,
            lhs,
            rhs,
        });
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
        res: impl Into<Reg>,
        ty: FcType,
        num_elems: impl Into<Option<u32>>,
        alignment: Alignment,
    ) {
        self.build_inst(Inst::Salloc {
            res: res.into(),
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
    fn load(&mut self, res: impl Into<Reg>, ty: FcType, pointer: Arg) {
        self.build_inst(Inst::Load {
            res: res.into(),
            ty,
            pointer,
        });
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
    /// - `true_args`: the arguments passed to the block `true_br`
    /// - `false_br`: the branch taken when `cond` evaluates to `false`
    /// - `false_args`: the arguments passed to the block `false_br`
    ///
    /// # Note
    ///
    /// Because this is a terminator, this terminator cannot have successors,
    /// so subsequent call to one of the [`InstBuilder`] method will have no
    /// effect.
    ///
    /// [`Br`]: crate::Terminator::Br
    fn br(
        &mut self,
        cond: Arg,
        true_br: BbLabel,
        true_args: impl IntoIterator<Item = Arg>,
        false_br: BbLabel,
        false_args: impl IntoIterator<Item = Arg>,
    ) {
        self.build_terminator(Terminator::Br {
            cond,
            true_br,
            true_args: true_args.into_iter().collect(),
            false_br,
            false_args: false_args.into_iter().collect(),
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
    /// - `true_args`: the arguments passed to the block `true_br`
    /// - `false_br`: the branch taken when the condition evaluates to `false`
    /// - `false_args`: the arguments passed to the block `false_br`
    ///
    /// # Note
    ///
    /// Because this is a terminator, this terminator cannot have successors,
    /// so subsequent call to one of the [`InstBuilder`] method will have no
    /// effect.
    ///
    /// [`BrIcmp`]: crate::Terminator::BrIcmp
    /// [comparison code]: crate::IntCC
    // NOTE: we ignore the clippy lint, because i think it's fine in this case i don't want to create an intermediate struct for it to not complain.
    #[allow(clippy::too_many_arguments)]
    fn br_icmp(
        &mut self,
        cc: IntCC,
        lhs: Arg,
        rhs: Arg,
        true_br: BbLabel,
        true_args: impl IntoIterator<Item = Arg>,
        false_br: BbLabel,
        false_args: impl IntoIterator<Item = Arg>,
    ) {
        self.build_terminator(Terminator::BrIcmp {
            cc,
            lhs,
            rhs,
            true_br,
            true_args: true_args.into_iter().collect(),
            false_br,
            false_args: false_args.into_iter().collect(),
        });
    }

    /// Build a [`Jump`] terminator.
    ///
    /// # Input
    ///
    /// - `dest`: the destination block
    /// - `args`: the block arguments passed to the block `dest`.
    ///
    /// # Note
    ///
    /// Because this is a terminator, this terminator cannot have successors,
    /// so subsequent call to one of the [`InstBuilder`] method will have no
    /// effect.
    ///
    /// [`Jump`]: crate::Terminator::Jump
    fn jump(&mut self, dest: BbLabel, args: impl IntoIterator<Item = Arg>) {
        self.build_terminator(Terminator::Jump {
            dest,
            args: args.into_iter().collect(),
        });
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
    fn ret(&mut self, ty: FcType, val: impl Into<Option<Arg>>) {
        self.build_terminator(Terminator::Ret {
            ty,
            val: val.into(),
        });
    }
}
