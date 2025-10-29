//! Pretty SIR printer.

use std::{
    fmt::{self, Display},
    io::{self, Write},
    rc::Rc,
    sync::Mutex,
};

use lunc_entity::Entity;
use lunc_utils::{
    join_pretty,
    pretty::{PrettyCtxt, PrettyDump},
};

use super::*;

/// Struct used to [`PrettyDump`] SIR.
#[derive(Debug, Clone)]
pub struct OrbDumper(Rc<Mutex<OrbDumperInner>>);

impl OrbDumper {
    /// Get access to an item.
    fn access_item<R>(&self, id: ItemId, mut accessor: impl FnMut(&Item) -> R) -> R {
        let inner = self.0.lock().unwrap();

        // SAFETY: lifetime of `orb` guaranteed by the creator of OrbDumpInner.
        unsafe { accessor((*inner.orb).items.get(id)) }
    }

    #[track_caller]
    fn current_body(&self) -> Option<&Body> {
        let inner = self.0.lock().unwrap();

        // SAFETY: lifetime of `orb` guaranteed by the creator of OrbDumpInner.
        unsafe {
            match (*inner.orb).items.get(inner.item?) {
                Item::Fundef(fundef) => Some(&fundef.body),
                Item::GlobalDef(globdef) => Some(&globdef.body),
                _ => None,
            }
        }
    }

    /// Set the current item id
    fn set_current_item(&self, id: ItemId) {
        let mut inner = self.0.lock().unwrap();

        inner.item = Some(id);
    }

    /// Is this temporary a parameter of a fundef?
    fn is_local_a_param(&self, local: LocalId) -> bool {
        if let Some(body) = self.current_body() {
            body.local_dbgs
                .get(local)
                .is_some_and(|dbg| dbg.kind == LocalKind::Param)
        } else {
            false
        }
    }
}

/// Internals of [`OrbDumper`].
#[derive(Debug, Clone)]
struct OrbDumperInner {
    // NOTE: we use a raw pointer because we cannot have lifetimes here.
    // SAFETY: orb must live for the entirety of its use and not have any
    // mutable pointer/reference.
    orb: *const Orb,
    /// current item
    item: Option<ItemId>,
}

impl<E> PrettyDump<E> for Orb {
    fn try_dump(&self, ctx: &mut PrettyCtxt, _: &E) -> io::Result<()> {
        let Orb { items } = self;

        let dumper = OrbDumper(Rc::new(Mutex::new(OrbDumperInner {
            orb: &raw const *self,
            item: None,
        })));

        for (id, item) in items.full_iter() {
            if id.index() != 0 {
                writeln!(ctx.out)?;
            }

            dumper.set_current_item(id);
            item.try_dump(ctx, &dumper)?;
        }

        Ok(())
    }
}

impl PrettyDump<OrbDumper> for Item {
    fn try_dump(&self, ctx: &mut PrettyCtxt, extra: &OrbDumper) -> io::Result<()> {
        match self {
            Item::Fundef(fundef) => fundef.try_dump(ctx, extra),
            Item::Fundecl(fundecl) => fundecl.try_dump(ctx, extra),
            Item::GlobalUninit(glob_uninit) => glob_uninit.try_dump(ctx, extra),
            Item::GlobalDef(globdef) => globdef.try_dump(ctx, extra),
        }
    }
}

impl PrettyDump<OrbDumper> for Fundef {
    fn try_dump(&self, ctx: &mut PrettyCtxt, extra: &OrbDumper) -> io::Result<()> {
        let Fundef {
            path,
            params,
            ret,
            body,
        } = self;

        write!(
            ctx.out,
            "<{}> :: fun({}) -> ",
            path,
            join_pretty(params, extra)
        )?;

        ret.try_dump(ctx, extra)?;

        body.try_dump(ctx, extra)?;

        Ok(())
    }
}

impl PrettyDump<OrbDumper> for Body {
    fn try_dump(&self, ctx: &mut PrettyCtxt, extra: &OrbDumper) -> io::Result<()> {
        let Body {
            locals,
            local_dbgs,
            comptime_bbs,
            bbs,
        } = self;

        writeln!(ctx.out, " {{")?;
        ctx.indent();

        for local in locals.data_iter() {
            // is this local a function parameter?
            let is_param = extra.is_local_a_param(local.id);
            // have we printed something about this local yet?
            let mut printed = false;

            if !is_param {
                local.try_dump(ctx, extra)?;
                printed = true;
            }

            if let Some(dbg) = local_dbgs.get(local.id) {
                dbg.try_dump(ctx, extra)?;
                printed = true;
            }

            if printed {
                writeln!(ctx.out)?;
            }
        }

        if !comptime_bbs.is_empty() && !locals.is_empty() && local_dbgs.get(locals.last()).is_none()
        {
            writeln!(ctx.out)?;
        }
        for bb in comptime_bbs.data_iter() {
            bb.try_dump(ctx, extra)?;
        }

        if !bbs.is_empty() && !comptime_bbs.is_empty() {
            writeln!(ctx.out)?;
        }
        for bb in bbs.data_iter() {
            bb.try_dump(ctx, extra)?;
        }

        writeln!(ctx.out, "}}")?;

        Ok(())
    }
}

impl PrettyDump<OrbDumper> for LocalId {
    fn try_dump(&self, ctx: &mut PrettyCtxt, extra: &OrbDumper) -> io::Result<()> {
        if self.index() == 0 {
            write!(ctx.out, "%RET")
        } else if let Some(body) = extra.current_body()
            && let Some(debug_info) = body.local_dbgs.get(*self)
        {
            write!(ctx.out, "%{}", debug_info.name)
        } else {
            write!(ctx.out, "%{}", self.index())
        }
    }
}

impl PrettyDump<OrbDumper> for Param {
    fn try_dump(&self, ctx: &mut PrettyCtxt, extra: &OrbDumper) -> io::Result<()> {
        let Param { local, typ } = self;

        local.try_dump(ctx, extra)?;
        write!(ctx.out, ": ")?;
        typ.try_dump(ctx, extra)?;

        Ok(())
    }
}

impl PrettyDump<OrbDumper> for Type {
    fn try_dump(&self, ctx: &mut PrettyCtxt, extra: &OrbDumper) -> io::Result<()> {
        match self {
            Type::PrimType(ptype) => write!(ctx.out, "{ptype}"),
            Type::Ptr(mutability, pointee) => {
                write!(ctx.out, "*{}", mutability.prefix_str())?;

                pointee.try_dump(ctx, extra)?;

                Ok(())
            }
            Type::FunPtr(params, ret) => {
                write!(ctx.out, "*fun({}) -> ", join_pretty(params, extra))?;

                ret.try_dump(ctx, extra)?;

                Ok(())
            }
            Type::FunDef {
                fundef,
                params,
                ret,
            } => {
                write!(ctx.out, "fun({}) -> ", join_pretty(params, extra))?;

                ret.try_dump(ctx, extra)?;

                extra.access_item(*fundef, |item| write!(ctx.out, " {{ {} }}", item.path()))?;

                Ok(())
            }
            Type::Local(local) => local.try_dump(ctx, extra),
            _ if self.is_dummy() => write!(ctx.out, "UNKNOWN"),
            Type::Item(id) => {
                extra.access_item(*id, |item| -> io::Result<()> {
                    write!(ctx.out, "<{}>", item.path())?;

                    Ok(())
                })?;

                Ok(())
            }
        }
    }
}

impl Display for PrimType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            PrimType::Isz => write!(f, "isz"),
            PrimType::I128 => write!(f, "i128"),
            PrimType::I64 => write!(f, "i64"),
            PrimType::I32 => write!(f, "i32"),
            PrimType::I16 => write!(f, "i16"),
            PrimType::I8 => write!(f, "i8"),
            PrimType::Usz => write!(f, "usz"),
            PrimType::U128 => write!(f, "u128"),
            PrimType::U64 => write!(f, "u64"),
            PrimType::U32 => write!(f, "u32"),
            PrimType::U16 => write!(f, "u16"),
            PrimType::U8 => write!(f, "u8"),
            PrimType::F128 => write!(f, "f128"),
            PrimType::F64 => write!(f, "f64"),
            PrimType::F32 => write!(f, "f32"),
            PrimType::F16 => write!(f, "f16"),
            PrimType::Bool => write!(f, "bool"),
            PrimType::Str => write!(f, "str"),
            PrimType::Char => write!(f, "char"),
            PrimType::Never => write!(f, "never"),
            PrimType::Void => write!(f, "void"),
            PrimType::Type => write!(f, "type"),
        }
    }
}

impl PrettyDump<OrbDumper> for Local {
    fn try_dump(&self, ctx: &mut PrettyCtxt, extra: &OrbDumper) -> io::Result<()> {
        let Local {
            comptime,
            id,
            mutability,
            typ,
        } = self;

        ctx.write_indent()?;

        write!(
            ctx.out,
            "{comptime}{mutability}",
            comptime = comptime.prefix_str(),
            mutability = mutability.prefix_str(),
        )?;
        id.try_dump(ctx, extra)?;
        write!(ctx.out, ": ")?;
        typ.try_dump(ctx, extra)?;
        writeln!(ctx.out, ";")?;

        Ok(())
    }
}

impl Display for LocalKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Binding => write!(f, ".Binding"),
            Self::Param => write!(f, ".Param"),
        }
    }
}

impl PrettyDump<OrbDumper> for LocalDbg {
    fn try_dump(&self, ctx: &mut PrettyCtxt, extra: &OrbDumper) -> io::Result<()> {
        // NOTE: name is not used because it was already been used in the Local
        // prettydump.
        let LocalDbg {
            id,
            name: _,
            kind,
            loc,
        } = self;

        ctx.write_indent()?;
        write!(ctx.out, "debug({}) ", kind)?;

        id.try_dump(ctx, extra)?;

        writeln!(ctx.out, " => {loc};")?;

        Ok(())
    }
}

impl PrettyDump<OrbDumper> for BasicBlock {
    fn try_dump(&self, ctx: &mut PrettyCtxt, extra: &OrbDumper) -> io::Result<()> {
        let BasicBlock {
            id,
            comptime,
            stmts,
            term,
        } = self;

        ctx.write_indent()?;

        writeln!(ctx.out, "{}{}: {{", comptime.prefix_str(), id)?;
        ctx.indent();

        for statement in stmts {
            statement.try_dump(ctx, extra)?;
        }

        ctx.write_indent()?;
        term.try_dump(ctx, extra)?;
        writeln!(ctx.out, ";")?;

        ctx.deindent();
        ctx.write_indent()?;
        writeln!(ctx.out, "}}")?;

        Ok(())
    }
}

impl Display for Bb {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.index() == 0 {
            write!(f, "@entry ")?;
        }

        write!(f, "BB{}", self.index())
    }
}

impl PrettyDump<OrbDumper> for Statement {
    fn try_dump(&self, ctx: &mut PrettyCtxt, extra: &OrbDumper) -> io::Result<()> {
        match self {
            Statement::Assignment(pvalue, rvalue) => {
                ctx.write_indent()?;
                pvalue.try_dump(ctx, extra)?;
                write!(ctx.out, " = ")?;
                rvalue.try_dump(ctx, extra)?;
                writeln!(ctx.out, ";")?;

                Ok(())
            }
        }
    }
}

impl PrettyDump<OrbDumper> for PValue {
    fn try_dump(&self, ctx: &mut PrettyCtxt, extra: &OrbDumper) -> io::Result<()> {
        match self {
            PValue::Local(local) => local.try_dump(ctx, extra),
            PValue::Item(id) => extra.access_item(*id, |item| -> io::Result<()> {
                write!(ctx.out, "<{}>", item.path())?;

                Ok(())
            }),
            PValue::Deref(pvalue) => {
                pvalue.try_dump(ctx, extra)?;

                write!(ctx.out, ".*")
            }
        }
    }
}

impl PrettyDump<OrbDumper> for RValue {
    fn try_dump(&self, ctx: &mut PrettyCtxt, extra: &OrbDumper) -> io::Result<()> {
        match self {
            RValue::Use(pvalue) => {
                write!(ctx.out, "use(")?;
                pvalue.try_dump(ctx, extra)?;
                write!(ctx.out, ")")?;

                Ok(())
            }
            RValue::Borrow(mutability, pvalue) => {
                write!(ctx.out, "&{}", mutability.prefix_str())?;
                pvalue.try_dump(ctx, extra)
            }
            RValue::Uint(int) => {
                write!(ctx.out, "u{}(", int.size_str())?;
                int.write_as_string_unsigned(&mut ctx.out)?;
                write!(ctx.out, ")")?;

                Ok(())
            }
            RValue::Sint(int) => {
                write!(ctx.out, "s{}(", int.size_str())?;
                int.write_as_string_signed(&mut ctx.out)?;
                write!(ctx.out, ")")?;

                Ok(())
            }
            RValue::Float(float) => {
                write!(ctx.out, "f{}(", float.size_str())?;
                float.write(&mut ctx.out)?;
                write!(ctx.out, ")")?;

                Ok(())
            }
            RValue::Bool(bool) => write!(ctx.out, "{bool}"),
            RValue::String(str, tag) => {
                if let Some(tag) = tag {
                    write!(ctx.out, "{tag}{str:?}")
                } else {
                    write!(ctx.out, "{str:?}")
                }
            }
            RValue::Type(typ) => typ.try_dump(ctx, extra),
            RValue::Cast(pvalue, typ) => {
                pvalue.try_dump(ctx, extra)?;
                write!(ctx.out, " as ")?;
                typ.try_dump(ctx, extra)?;

                Ok(())
            }
            RValue::Binary(lhs, op, rhs) => {
                lhs.try_dump(ctx, extra)?;
                write!(ctx.out, " {} ", op.op_str())?;
                rhs.try_dump(ctx, extra)?;

                Ok(())
            }
            RValue::Unary(op, pvalue) => {
                write!(ctx.out, "{}", op.op_str())?;
                pvalue.try_dump(ctx, extra)
            }
            RValue::Call { callee, args } => {
                write!(ctx.out, "call(")?;
                callee.try_dump(ctx, extra)?;
                write!(ctx.out, ", ({}))", join_pretty(args, extra))?;

                Ok(())
            }
            RValue::Nothing => {
                write!(ctx.out, "nothing")
            }
        }
    }
}

impl PrettyDump<OrbDumper> for Terminator {
    fn try_dump(&self, ctx: &mut PrettyCtxt, extra: &OrbDumper) -> io::Result<()> {
        match self {
            Terminator::Goto(bb) => {
                write!(ctx.out, "goto({bb})")
            }
            Terminator::If(pvalue, bb0, bb1) => {
                write!(ctx.out, "if ")?;
                pvalue.try_dump(ctx, extra)?;
                write!(ctx.out, " {{ {bb0} }} else {{ {bb1} }}")?;

                Ok(())
            }
            Terminator::Return => {
                write!(ctx.out, "return")
            }
            Terminator::Unreachable => {
                write!(ctx.out, "unreachable")
            }
        }
    }
}

impl PrettyDump<OrbDumper> for Fundecl {
    fn try_dump(&self, ctx: &mut PrettyCtxt, extra: &OrbDumper) -> io::Result<()> {
        let Fundecl {
            path,
            abi,
            name,
            params,
            ret,
        } = self;

        write!(
            ctx.out,
            "<{}> :: extern {}, name {:?} fun({}) -> ",
            path,
            abi.enum_str(),
            name,
            join_pretty(params, extra)
        )?;

        ret.try_dump(ctx, extra)?;
        writeln!(ctx.out, ";")?;

        Ok(())
    }
}

impl PrettyDump<OrbDumper> for GlobalUninit {
    fn try_dump(&self, ctx: &mut PrettyCtxt, extra: &OrbDumper) -> io::Result<()> {
        let GlobalUninit { path, typ, name } = self;

        write!(ctx.out, "<{}> : ", path)?;
        typ.try_dump(ctx, extra)?;
        writeln!(ctx.out, ", name {:?};", name)?;

        Ok(())
    }
}

impl PrettyDump<OrbDumper> for GlobalDef {
    fn try_dump(&self, ctx: &mut PrettyCtxt, extra: &OrbDumper) -> io::Result<()> {
        let GlobalDef { path, typ, body } = self;

        write!(ctx.out, "<{}> : ", path)?;
        typ.try_dump(ctx, extra)?;
        write!(ctx.out, " =")?;
        body.try_dump(ctx, extra)?;

        Ok(())
    }
}
