//! FIR verifier, verifies that the FIR is well formed and correct.
//!
//! It is **STRONGLY** recommended to run the verifier before optimization and
//! code generation, unless you can guarantee that the FIR you built is well
//! formed and correct.

use std::{collections::HashMap, error::Error, iter::zip};

use lunc_utils::is_pow2;
use thiserror::Error;

use super::*;

/// Verifier error
#[derive(Debug, Clone)]
pub struct VerifierError {
    backtrace: Vec<Trace>,
    error: VerifierErrorVariant,
}

impl Display for VerifierError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for trace in &self.backtrace {
            writeln!(f, "In {trace},")?;
        }

        write!(f, "\nERROR: {}", self.error)?;
        Ok(())
    }
}

impl Error for VerifierError {
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        Some(&self.error)
    }
}

/// Trace of a [`VerifierError`].
#[derive(Debug, Clone)]
pub enum Trace {
    Item { name: Name },
    Bb { bb: BbLabel },
    Inst { nth: usize },
    Terminator,
}

impl Display for Trace {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Item { name } => write!(f, "fir item {name}"),
            Self::Bb { bb } => write!(f, "basic block {bb}"),
            Self::Inst { nth } => write!(f, "the {nth}-th instruction"),
            Self::Terminator => write!(f, "the terminator instruction"),
        }
    }
}

/// Verifier error variant.
#[derive(Debug, Clone, Error)]
pub enum VerifierErrorVariant {
    #[error("{name} was defined more than once")]
    NameDefinedMoreThanOnce { name: Name },
    #[error("invalid basic block entry for function definition {fundef}")]
    InvalidEntry { fundef: Name },
    #[error(
        "the arguments of the basic block entry doesn't match the arguments of \
        the fundef {fundef}."
    )]
    InvalidEntryArgs { fundef: Name },
    #[error("the register {reg} was assigned more than once.")]
    RegAssignedMoreThanOnce { reg: Reg },
    #[error("the type of the 'funptr' field of the call inst is {got} instead of a funptr")]
    NotFunptrInCall { got: FcType },
    #[error("the arguments of the call instruction do not match the definition")]
    CallArgsNonMatching,
    #[error("the type of the call instruction doesn't match the return type of the funptr")]
    CallTypeAndDefNonMatching,
    #[error("type mismatched")]
    TypeMismatch,
    #[error("the type {typ} is invalid for this instruction")]
    InvalidType { typ: FcType },
    #[error("a string constant is invalid inside of an argument")]
    StringConstantInArg,
    #[error("invalid alignment {alignment} for type {typ}")]
    InvalidAlignment { typ: FcType, alignment: u32 },
    #[error("not a pointer in a memory instruction")]
    NonPtrInMemInst,
    #[error("the arguments of the basic block {bb} doesn't match with what was passed")]
    BbArgsTypeMismatch { bb: BbLabel },
}

use VerifierErrorVariant::*;

type Result<T = (), E = VerifierError> = std::result::Result<T, E>;

/// FIR Item.
#[derive(Debug, Clone)]
pub enum FirItem {
    FunDef(FunDef),
    FunDecl(FunDecl),
    Glob(Glob),
}

/// [`FirUnit`] verifier.
#[derive(Debug, Clone)]
pub struct FirUnitVerifier<'fir> {
    /// the unit being checked
    ///
    /// # Note
    ///
    /// Mutating this field if not done properly could cause bugs.
    unit: &'fir FirUnit,
    /// items of FIR
    items: HashMap<Name, FirItem>,
    /// basic blocks arguments of the current function definition
    bb_args: HashMap<BbLabel, Vec<FcType>>,
    /// registers of the current basic block of the current function definition
    regs: HashMap<Reg, FcType>,
    /// current function definition's name
    current_fundef: Option<Name>,
    /// current bb label of the current function
    current_bb: Option<BbLabel>,
    /// current backtrace.
    current_backtrace: Vec<Trace>,
    /// pointer width
    ptr_width: PtrWidth,
    /// the current function return type.
    funret: Option<FcType>,
}

impl<'fir> FirUnitVerifier<'fir> {
    /// Create a new FIR unit verifier
    pub fn new(unit: &'fir FirUnit, ptr_width: PtrWidth) -> FirUnitVerifier<'fir> {
        FirUnitVerifier {
            unit,
            items: HashMap::with_capacity(
                unit.globals.len() + unit.fundecls.len() + unit.fundefs.len(),
            ),
            bb_args: HashMap::new(),
            regs: HashMap::new(),
            current_fundef: None,
            current_bb: None,
            current_backtrace: Vec::new(),
            ptr_width,
            funret: None,
        }
    }

    /// returns the current function definition
    pub fn current_fundef(&self) -> &Name {
        self.current_fundef.as_ref().unwrap()
    }

    /// returns the current basic block
    pub fn current_bb(&self) -> BbLabel {
        self.current_bb.unwrap()
    }

    fn error<T>(&self, error: VerifierErrorVariant) -> Result<T> {
        Err(VerifierError {
            backtrace: self.current_backtrace.clone(),
            error,
        })
    }

    /// Verifies the [`FirUnit`] returns an [`Err`] if it failed to verify.
    pub fn verify(&mut self) -> Result {
        // 1. insert all the items and ensure there is no item with the same
        //    name
        for glob in &self.unit.globals {
            let name = glob.inspect(|this| this.name.clone());

            if self.items.contains_key(&name) {
                return self.error(NameDefinedMoreThanOnce { name });
            }

            self.items.insert(name, FirItem::Glob(glob.clone()));
        }

        for fundef in &self.unit.fundefs {
            let name = fundef.inspect(|this| this.name.clone());

            if self.items.contains_key(&name) {
                return self.error(NameDefinedMoreThanOnce { name });
            }

            self.items.insert(name, FirItem::FunDef(fundef.clone()));
        }

        for fundecl in &self.unit.fundecls {
            let name = fundecl.inspect(|this| this.name.clone());

            if self.items.contains_key(&name) {
                return self.error(NameDefinedMoreThanOnce { name });
            }

            self.items.insert(name, FirItem::FunDecl(fundecl.clone()));
        }

        // 2. verify the content of every FunDef bodies.
        for fundef in &self.unit.fundefs {
            self.current_backtrace.push(Trace::Item {
                name: fundef.inspect(|this| this.name.clone()),
            });

            self.verify_fundef(fundef)?;

            self.current_backtrace.pop();
        }

        // 2. verify the content of every FunDef bodies.
        for glob in &self.unit.globals {
            self.current_backtrace.push(Trace::Item {
                name: glob.inspect(|this| this.name.clone()),
            });

            self.verify_glob(glob)?;

            self.current_backtrace.pop();
        }

        Ok(())
    }

    /// Verifies a function definition
    pub fn verify_fundef(&mut self, fundef: &FunDef) -> Result {
        // cleans the arguments of the bbs
        self.bb_args.clear();

        let fundef_name = || fundef.inspect(|this| this.name.clone());

        // set the current values for this fundef
        self.current_fundef = Some(fundef_name());
        self.funret = Some(fundef.inspect(|this| this.ret.clone()));

        // is the entry present
        let entry_present = fundef.inspect(|this| {
            this.bbs
                .first()
                .map(|bb| bb.label() == BbLabel::ENTRY)
                .unwrap_or(false)
        });

        if !entry_present {
            return self.error(InvalidEntry {
                fundef: fundef_name(),
            });
        }

        // does the entry has the same args as the fundef
        let entry = fundef.inspect(|this| this.bbs.first().unwrap().clone());

        if entry.inspect(|entry| fundef.inspect(|fun| entry.args != fun.args)) {
            return self.error(InvalidEntryArgs {
                fundef: fundef_name(),
            });
        }

        // insert the bb and their args in bb_args
        fundef.inspect(|this| {
            for bb in &this.bbs {
                self.bb_args
                    .insert(bb.label(), bb.inspect(|bb| bb.args.clone()));
            }
        });

        // verify the bb
        fundef.inspect(|this| -> Result {
            for bb in &this.bbs {
                self.current_backtrace.push(Trace::Bb { bb: bb.label() });

                self.verify_bb(bb)?;

                self.current_backtrace.pop();
            }

            Ok(())
        })?;

        // reset the current fundef values
        self.current_fundef = None;
        self.funret = None;

        Ok(())
    }

    /// Verify a basic block
    pub fn verify_bb(&mut self, bb: &BasicBlock) -> Result {
        self.current_bb = Some(bb.label());
        self.regs.clear();

        bb.inspect(|this| -> Result {
            for (nth_arg, arg) in this.args.iter().enumerate() {
                self.regs.insert(Reg::new(nth_arg as u32 + 1), arg.clone());
            }

            for (nth, inst) in this.insts.iter().enumerate() {
                self.current_backtrace.push(Trace::Inst { nth });

                self.verify_inst(inst)?;

                self.current_backtrace.pop();
            }

            self.current_backtrace.push(Trace::Terminator);

            self.verify_terminator(this.terminator.as_ref().unwrap())?;

            self.current_backtrace.pop();

            Ok(())
        })?;

        self.current_bb = None;

        Ok(())
    }

    /// Verify an instruction
    pub fn verify_inst(&mut self, inst: &Inst) -> Result {
        let inst_typ: Option<FcType>;

        match inst {
            Inst::Call {
                res: _,
                ty,
                fnptr,
                args,
            } => {
                inst_typ = Some(ty.clone());

                let funptr_typ = self.arg_type(fnptr)?;

                let FcType::FunPtr {
                    args: expected_args,
                    ret,
                } = funptr_typ
                else {
                    return self.error(NotFunptrInCall { got: funptr_typ });
                };

                let args_typ = args
                    .iter()
                    .map(|arg| self.arg_type(arg).unwrap())
                    .collect::<Vec<_>>();

                for (expected, got) in zip(expected_args, args_typ) {
                    if !expected.type_eq(&got) {
                        return self.error(CallArgsNonMatching);
                    }
                }

                if !ret.type_eq(ty) {
                    return self.error(CallTypeAndDefNonMatching);
                }
            }
            Inst::Add {
                res: _,
                ty,
                lhs,
                rhs,
            }
            | Inst::Fadd {
                res: _,
                ty,
                lhs,
                rhs,
            }
            | Inst::Sub {
                res: _,
                ty,
                lhs,
                rhs,
            }
            | Inst::Fsub {
                res: _,
                ty,
                lhs,
                rhs,
            }
            | Inst::Mul {
                res: _,
                ty,
                lhs,
                rhs,
            }
            | Inst::Fmul {
                res: _,
                ty,
                lhs,
                rhs,
            }
            | Inst::Udiv {
                res: _,
                ty,
                lhs,
                rhs,
            }
            | Inst::Sdiv {
                res: _,
                ty,
                lhs,
                rhs,
            }
            | Inst::Fdiv {
                res: _,
                ty,
                lhs,
                rhs,
            }
            | Inst::Urem {
                res: _,
                ty,
                lhs,
                rhs,
            }
            | Inst::Srem {
                res: _,
                ty,
                lhs,
                rhs,
            }
            | Inst::Frem {
                res: _,
                ty,
                lhs,
                rhs,
            }
            | Inst::And {
                res: _,
                ty,
                lhs,
                rhs,
            }
            | Inst::Xor {
                res: _,
                ty,
                lhs,
                rhs,
            }
            | Inst::Or {
                res: _,
                ty,
                lhs,
                rhs,
            }
            | Inst::Shr {
                res: _,
                ty,
                lhs,
                rhs,
            }
            | Inst::Shl {
                res: _,
                ty,
                lhs,
                rhs,
            } => {
                inst_typ = Some(ty.clone());

                let lhs_typ = self.arg_type(lhs)?;

                if lhs_typ != self.arg_type(rhs)? || lhs_typ != *ty {
                    return self.error(TypeMismatch);
                }

                if inst.is_binop_float() && !ty.is_float()
                    || inst.is_binop_int() && !ty.is_int()
                    || inst.is_binop_sint() && !ty.is_sint()
                    || inst.is_binop_uint() && !ty.is_uint()
                {
                    return self.error(InvalidType { typ: ty.clone() });
                }
            }
            Inst::Neg { res: _, ty, op } => {
                inst_typ = Some(ty.clone());

                let op_ty = self.arg_type(op)?;

                if *ty != op_ty {
                    return self.error(TypeMismatch);
                } else if !ty.is_int() {
                    return self.error(InvalidType { typ: ty.clone() });
                }
            }
            Inst::Fneg { res: _, ty, op } => {
                inst_typ = Some(ty.clone());

                let op_ty = self.arg_type(op)?;

                if *ty != op_ty {
                    return self.error(TypeMismatch);
                } else if !ty.is_float() {
                    return self.error(InvalidType { typ: ty.clone() });
                }
            }
            Inst::Icmp {
                res: _,
                cc: _,
                lhs,
                rhs,
            } => {
                inst_typ = Some(FcType::Bool);

                let lhs_typ = self.arg_type(lhs)?;

                if !lhs_typ.type_eq(&self.arg_type(rhs)?) {
                    return self.error(TypeMismatch);
                } else if !lhs_typ.is_int() {
                    return self.error(InvalidType {
                        typ: lhs_typ.clone(),
                    });
                }
            }
            Inst::Salloc {
                res: _,
                ty,
                num_elems: _,
                alignment,
            } => {
                inst_typ = Some(FcType::ptr(ty.clone()));

                if !is_pow2(*alignment) || *alignment >= ty.align(self.ptr_width) {
                    return self.error(InvalidAlignment {
                        typ: ty.clone(),
                        alignment: *alignment,
                    });
                }
            }
            Inst::Load {
                res: _,
                ty,
                pointer,
            } => {
                inst_typ = Some(ty.clone());

                let (FcType::Ptr { ty: pointee_type }
                | FcType::Array {
                    n: _,
                    ty: pointee_type,
                }) = self.arg_type(pointer)?
                else {
                    return self.error(NonPtrInMemInst);
                };

                if !pointee_type.type_eq(ty) {
                    return self.error(TypeMismatch);
                }
            }
            Inst::Store { ty, val, pointer } => {
                inst_typ = None;

                let (FcType::Ptr { ty: pointee_type }
                | FcType::Array {
                    n: _,
                    ty: pointee_type,
                }) = self.arg_type(pointer)?
                else {
                    return self.error(NonPtrInMemInst);
                };

                if !self.arg_type(val)?.type_eq(ty) || &*pointee_type != ty {
                    return self.error(TypeMismatch);
                }
            }
        }

        if let Some(res) = inst.res() {
            if self.regs.contains_key(&res) {
                return self.error(RegAssignedMoreThanOnce { reg: res });
            }

            self.regs.insert(res, inst_typ.unwrap().clone());
        }

        Ok(())
    }

    /// Verifies arguments (`args`) passed to a basic block (`bb`).
    pub fn verify_bb_args(&mut self, bb: BbLabel, args: &[Arg]) -> Result {
        let expected_args = self.bb_args.get(&bb).expect("BB doesn't exist");

        let args_typ = args
            .iter()
            .map(|arg| self.arg_type(arg).unwrap())
            .collect::<Vec<_>>();

        for (expected, got) in zip(expected_args, args_typ) {
            if !expected.type_eq(&got) {
                return self.error(BbArgsTypeMismatch { bb });
            }
        }

        Ok(())
    }

    /// Verifies a [`Terminator`].
    pub fn verify_terminator(&mut self, terminator: &Terminator) -> Result {
        match terminator {
            Terminator::Br {
                cond,
                true_br,
                true_args,
                false_br,
                false_args,
            } => {
                if !self.arg_type(cond)?.type_eq(&FcType::Bool) {
                    return self.error(TypeMismatch);
                }

                self.verify_bb_args(*true_br, true_args)?;
                self.verify_bb_args(*false_br, false_args)?;
            }
            Terminator::BrIcmp {
                cc: _,
                lhs,
                rhs,
                true_br,
                true_args,
                false_br,
                false_args,
            } => {
                let lhs_typ = self.arg_type(lhs)?;

                if !lhs_typ.type_eq(&self.arg_type(rhs)?) {
                    return self.error(TypeMismatch);
                } else if !lhs_typ.is_int() {
                    return self.error(InvalidType {
                        typ: lhs_typ.clone(),
                    });
                }

                self.verify_bb_args(*true_br, true_args)?;
                self.verify_bb_args(*false_br, false_args)?;
            }
            Terminator::Jump { dest, args } => {
                self.verify_bb_args(*dest, args)?;
            }
            Terminator::Ret { ty, val } => {
                if !ty.type_eq(self.funret.as_ref().unwrap()) {
                    return self.error(TypeMismatch);
                } else if let Some(val) = val
                    && !self.arg_type(val)?.type_eq(ty)
                {
                    return self.error(TypeMismatch);
                }
            }
        }

        Ok(())
    }

    pub fn verify_glob(&mut self, glob: &Glob) -> Result {
        glob.inspect(|glob| -> Result {
            let val_typ = glob.val.typ();

            if !val_typ.type_eq(&glob.ty) {
                return self.error(TypeMismatch);
            }

            Ok(())
        })
    }

    /// Returns the type of an argument
    ///
    /// if `is_const` is set to false and the `arg` is a constant
    /// [`ConstValue::String`] this function returns an error.
    ///
    /// [`ConstValue::String`]: crate::ConstValue::String
    pub fn arg_type(&self, arg: &Arg) -> Result<FcType> {
        if matches!(arg, Arg::Constant(ConstValue::String(_))) {
            return self.error(StringConstantInArg);
        }

        match arg {
            Arg::Constant(cval) => Ok(cval.typ()),
            Arg::Reg(reg) => Ok(self.regs.get(reg).unwrap().clone()),
            Arg::Glob(glob) => Ok(glob.inspect(|this| this.ty.clone())),
            Arg::Fun(fundef) => Ok(FcType::funptr(fundef.clone_args(), fundef.clone_ret())),
        }
    }
}
