//! SIR building helping structs.

use lunc_ast::{Comptime, Mutability};
use lunc_entity::EntityDb;

use crate::sir::*;

/// Where to put the [RValue]?
pub trait Place {
    /// Result to output to the user.
    type Res;

    /// Create a statement from the args.
    fn create_statement(
        self,
        localable: &mut dyn LocalAble,
        value: RValue,
        comptime: Comptime,
    ) -> (Statement, Self::Res);
}

/// A [Place] that assigns the [RValue] creates a temporary [Local] (with dummy
/// type) and returns it.
pub struct InTemp;

impl Place for InTemp {
    type Res = LocalId;

    fn create_statement(
        self,
        localable: &mut dyn LocalAble,
        value: RValue,
        comptime: Comptime,
    ) -> (Statement, Self::Res) {
        let temp = localable.new_local(comptime, Mutability::Not, Type::dummy());
        let stmt = Statement::Assignment(PValue::Local(temp), value);

        (stmt, temp)
    }
}

impl Place for PValue {
    type Res = ();

    fn create_statement(
        self,
        _: &mut dyn LocalAble,
        value: RValue,
        _: Comptime,
    ) -> (Statement, Self::Res) {
        let stmt = Statement::Assignment(self, value);

        (stmt, ())
    }
}

impl Place for LocalId {
    type Res = ();

    fn create_statement(
        self,
        _: &mut dyn LocalAble,
        value: RValue,
        _: Comptime,
    ) -> (Statement, Self::Res) {
        let stmt = Statement::Assignment(PValue::Local(self), value);

        (stmt, ())
    }
}

impl Place for ItemId {
    type Res = ();

    fn create_statement(
        self,
        _: &mut dyn LocalAble,
        value: RValue,
        _: Comptime,
    ) -> (Statement, Self::Res) {
        let stmt = Statement::Assignment(PValue::Item(self), value);

        (stmt, ())
    }
}

/// SIR builder for a compile-time body, [CtBody].
#[derive(Debug)]
pub struct CtBuilder<'body> {
    pub(crate) body: &'body mut dyn CtBody,
    /// current basic-block
    bb: Bb,
}

impl<'body> BuilderBase for CtBuilder<'body> {
    fn bbs(&self) -> &EntityDb<Bb> {
        self.body.ct_blocks()
    }

    fn bbs_mut(&mut self) -> &mut EntityDb<Bb> {
        self.body.ct_blocks_mut()
    }

    fn current_bb(&self) -> Bb {
        self.bb
    }

    fn localable(&self) -> &dyn LocalAble {
        self.body
    }

    fn localable_mut(&mut self) -> &mut dyn LocalAble {
        self.body
    }

    #[inline(always)]
    fn comptime(&self) -> Comptime {
        Comptime::Yes
    }
}

impl<'body> SirBuilder for CtBuilder<'body> {}

/// SIR builder for the runtime body, [CrtBody].
#[derive(Debug)]
pub struct RtBuilder<'body> {
    pub(crate) body: &'body mut dyn CrtBody,
    /// current basic-block
    bb: Bb,
}

impl<'body> BuilderBase for RtBuilder<'body> {
    fn bbs(&self) -> &EntityDb<Bb> {
        self.body.blocks()
    }

    fn bbs_mut(&mut self) -> &mut EntityDb<Bb> {
        self.body.blocks_mut()
    }

    fn current_bb(&self) -> Bb {
        self.bb
    }

    fn localable(&self) -> &dyn LocalAble {
        self.body
    }

    fn localable_mut(&mut self) -> &mut dyn LocalAble {
        self.body
    }

    #[inline(always)]
    fn comptime(&self) -> Comptime {
        Comptime::No
    }
}

impl<'body> SirBuilder for RtBuilder<'body> {}

/// Base trait helping for [SirBuilder].
pub trait BuilderBase {
    /// Get the basic-blocks.
    fn bbs(&self) -> &EntityDb<Bb>;

    /// Mutable `BuilderBase::bbs`.
    fn bbs_mut(&mut self) -> &mut EntityDb<Bb>;

    /// Get the current basic-block.
    fn current_bb(&self) -> Bb;

    /// Get the [LocalAble] of the body.
    fn localable(&self) -> &dyn LocalAble;

    /// Mutable [`BuilderBase::localable`].
    fn localable_mut(&mut self) -> &mut dyn LocalAble;

    /// Is this builder comptime?
    fn comptime(&self) -> Comptime;

    /// Appends `stmt` at the end of the current basic-block.
    fn append_stmt<P: Place>(&mut self, place: P, rvalue: RValue) -> P::Res {
        let comptime = self.comptime();

        let (stmt, res) = place.create_statement(self.localable_mut(), rvalue, comptime);

        let bb = self.current_bb();

        self.bbs_mut().get_mut(bb).stmts.push(stmt);

        res
    }

    fn set_terminator(&mut self, term: Terminator) {
        let bb = self.current_bb();

        assert!(
            self.bbs().get(bb).term.is_none(),
            "terminator for basic-block is already set."
        );

        self.bbs_mut().get_mut(bb).term = Some(term);
    }
}

/// Helping struct to build a SIR-body ([CtBody] or [CrtBody])
///
/// To create a new SirBuilder, use the constructors one the Body:
/// [`Body::builder`], [`Body::ct_builder`], [`CtoBody::builder`].
///
/// Or the methods on the item directly: [`Fundef::builder`],
/// [`Fundef::ct_builder`]..
pub trait SirBuilder: BuilderBase {
    /// Append a new `use(PVALUE)` statement to the current basic block.
    ///
    /// Where:
    /// - `place` is a constructor of a statement, that will hold the
    ///   [RValue::Use].
    /// - `pvalue` the value that will be read, `PVALUE`.
    fn use_<P: Place>(&mut self, place: P, pvalue: PValue) -> P::Res {
        self.append_stmt(place, RValue::Use(pvalue))
    }

    /// Append a new `& mut? PVALUE` statement to the current basic block.
    ///
    /// Where:
    /// - `place` is a constructor of a statement, that will hold the
    ///   [RValue::Borrow].
    /// - `mutability`, the mutability of the borrow, `mut?`
    /// - `pvalue` the value that will be borrowed, `PVALUE`.
    fn borrow<P: Place>(&mut self, place: P, mutability: Mutability, pvalue: PValue) -> P::Res {
        self.append_stmt(place, RValue::Borrow(mutability, pvalue))
    }

    /// Append a new `UINT` statement to the current basic block.
    ///
    /// Where:
    /// - `place` is a constructor of a statement, that will hold the
    ///   [RValue::Uint].
    /// - `imm`, the immediate value.
    fn uint<P: Place>(&mut self, place: P, imm: impl Into<Int>) -> P::Res {
        self.append_stmt(place, RValue::Uint(imm.into()))
    }

    /// Append a new `SINT` statement to the current basic block.
    ///
    /// Where:
    /// - `place` is a constructor of a statement, that will hold the
    ///   [RValue::Sint].
    /// - `imm`, the immediate value.
    fn sint<P: Place>(&mut self, place: P, imm: impl Into<Int>) -> P::Res {
        self.append_stmt(place, RValue::Sint(imm.into()))
    }

    /// Append a new `FLOAT` statement to the current basic block.
    ///
    /// Where:
    /// - `place` is a constructor of a statement, that will hold the
    ///   [RValue::Float].
    /// - `imm`, the immediate value.
    fn float<P: Place>(&mut self, place: P, imm: impl Into<Float>) -> P::Res {
        self.append_stmt(place, RValue::Float(imm.into()))
    }

    /// Append a new `BOOL` statement to the current basic block.
    ///
    /// Where:
    /// - `place` is a constructor of a statement, that will hold the
    ///   [RValue::Bool].
    /// - `imm`, the immediate value.
    fn bool<P: Place>(&mut self, place: P, imm: bool) -> P::Res {
        self.append_stmt(place, RValue::Bool(imm))
    }

    /// Append a new `STRING` statement to the current basic block.
    ///
    /// Where:
    /// - `place` is a constructor of a statement, that will hold the
    ///   [RValue::String].
    /// - `imm`, the immediate value.
    fn string<P: Place>(&mut self, place: P, imm: impl ToString) -> P::Res {
        self.append_stmt(place, RValue::String(imm.to_string()))
    }

    /// Append a new `TYPE` statement to the current basic block.
    ///
    /// Where:
    /// - `place` is a constructor of a statement, that will hold the
    ///   [RValue::Type].
    /// - `typ`, the type.
    fn type_<P: Place>(&mut self, place: P, typ: Type) -> P::Res {
        self.append_stmt(place, RValue::Type(typ))
    }

    /// Append a new `PVALUE as TYPE` statement to the current basic block.
    ///
    /// Where:
    /// - `place` is a constructor of a statement, that will hold the
    ///   [RValue::Cast].
    /// - `pvalue`, the value to cast.
    /// - `typ`, the type to which we cast.
    fn cast<P: Place>(&mut self, place: P, pvalue: PValue, typ: Type) -> P::Res {
        self.append_stmt(place, RValue::Cast(pvalue, typ))
    }

    /// Append a new `PVALUE0 <binop> PVALUE1` statement to the current basic block.
    ///
    /// Where:
    /// - `place` is a constructor of a statement, that will hold the
    ///   [RValue::Binary].
    /// - `pvalue0`, the right-hand side of the operation.
    /// - `op`, the binary operation.
    /// - `pvalue1`, the left-hand side of the operation.
    fn binary<P: Place>(
        &mut self,
        place: P,
        pvalue0: PValue,
        op: BinOp,
        pvalue1: PValue,
    ) -> P::Res {
        self.append_stmt(place, RValue::Binary(pvalue0, op, pvalue1))
    }

    /// Append a new `<unop> PVALUE` statement to the current basic block.
    ///
    /// Where:
    /// - `place` is a constructor of a statement, that will hold the
    ///   [RValue::Unary].
    /// - `op`, the binary operation.
    /// - `pvalue`, the left-hand side of the operation.
    fn unary<P: Place>(&mut self, place: P, op: UnOp, pvalue: PValue) -> P::Res {
        self.append_stmt(place, RValue::Unary(op, pvalue))
    }

    /// Append a new `call(PVALUE0, (PVALUE1..))` statement to the current basic
    /// block.
    ///
    /// Where:
    /// - `place` is a constructor of a statement, that will hold the
    ///   [RValue::Call].
    /// - `callee` is `PVALUE0`, the thing getting called
    /// - `args` (`PVALUE1..`) an iterator of the arguments to call the function
    ///   with.
    fn call<P: Place>(
        &mut self,
        place: P,
        callee: PValue,
        args: impl IntoIterator<Item = PValue>,
    ) -> P::Res {
        self.append_stmt(
            place,
            RValue::Call {
                callee,
                args: args.into_iter().collect(),
            },
        )
    }

    /// Append a new `nothing` statement to the current basic block.
    ///
    /// Where:
    /// - `place` is a constructor of a statement, that will hold the
    ///   [RValue::Nothing].
    fn nothing<P: Place>(&mut self, place: P) -> P::Res {
        self.append_stmt(place, RValue::Nothing)
    }

    /// Set the terminator of the current basic-block to <code>[goto]\(bb\)</code>.
    ///
    /// [goto]: Terminator::Goto
    fn goto(&mut self, bb: Bb) {
        self.set_terminator(Terminator::Goto(bb));
    }

    /// Set the terminator of the current basic-block to
    /// <code>[if] PVALUE { bb0 } else { bb1 }</code>.
    ///
    /// [if]: Terminator::If
    fn if_(&mut self, pvalue: PValue, bb0: Bb, bb1: Bb) {
        self.set_terminator(Terminator::If(pvalue, bb0, bb1));
    }

    /// Set the terminator of the current basic-block to
    /// <code>[return]</code>.
    ///
    /// [return]: Terminator::Return
    fn ret(&mut self) {
        self.set_terminator(Terminator::Return);
    }

    /// Set the terminator of the current basic-block to
    /// <code>[unreachable]</code>.
    ///
    /// [unreachable]: Terminator::Unreachable
    fn unreachable(&mut self) {
        self.set_terminator(Terminator::Unreachable);
    }
}
