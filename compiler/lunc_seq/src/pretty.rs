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
    pub fn access_item<R>(&self, id: ItemId, mut accessor: impl FnMut(&Item) -> R) -> R {
        let inner = self.0.lock().unwrap();

        // SAFETY: lifetime of `orb` guaranteed by the creator of OrbDumpInner.
        unsafe { accessor((*inner.orb).items.get(id)) }
    }

    /// Get access to a binding in the current item.
    pub fn access_bindings<R>(&self, id: BindingId, mut accessor: impl FnMut(&Binding) -> R) -> R {
        let inner = self.0.lock().unwrap();

        // SAFETY: lifetime of `orb` guaranteed by the creator of OrbDumpInner.
        let body = unsafe {
            match inner.item {
                Some(item_id) => match (*inner.orb).items.get(item_id) {
                    Item::Fundef(fundef) => &fundef.body,
                    _ => panic!("no body for this item kind."),
                },
                None => panic!("no current item"),
            }
        };

        accessor(body.bindings.get(id))
    }

    /// Set the current item id
    pub fn set_current_item(&self, id: ItemId) {
        let mut inner = self.0.lock().unwrap();

        inner.item = Some(id);
    }

    /// Is this temporary a parameter of a fundef?
    pub fn is_tmp_a_param(&self, tmp: Tmp) -> bool {
        let inner = self.0.lock().unwrap();

        if let Some(id) = inner.item
            // SAFETY: lifetime of `orb` guaranteed by the creator of OrbDumpInner.
            && let Item::Fundef(fundef) = unsafe { (*inner.orb).items.get(id) }
        {
            let temporary = fundef.body.temporaries.get(tmp);
            let range = 1..=fundef.params.len();

            range.contains(&temporary.id.index())
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
            bindings,
            temporaries,
            comptime_bbs,
            bbs,
        } = self;

        writeln!(ctx.out, " {{")?;
        ctx.indent();

        for binding in bindings.data_iter() {
            binding.try_dump(ctx, extra)?;
        }

        if !temporaries.is_empty() && !bindings.is_empty() {
            writeln!(ctx.out)?;
        }
        for temporary in temporaries.data_iter() {
            if extra.is_tmp_a_param(temporary.id) {
                // the temporary is a parameter, it's already defined.
                continue;
            }

            temporary.try_dump(ctx, extra)?;
        }

        if !comptime_bbs.is_empty() && !temporaries.is_empty() {
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

impl PrettyDump<OrbDumper> for Param {
    fn try_dump(&self, ctx: &mut PrettyCtxt, extra: &OrbDumper) -> io::Result<()> {
        let Param { tmp, typ } = self;

        write!(ctx.out, "{}: ", tmp)?;

        typ.try_dump(ctx, extra)?;

        Ok(())
    }
}

impl Display for Tmp {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.index() == 0 {
            write!(f, "%RET")
        } else {
            write!(f, "%{}", self.index())
        }
    }
}

impl PrettyDump<OrbDumper> for Type {
    fn try_dump(&self, ctx: &mut PrettyCtxt, extra: &OrbDumper) -> io::Result<()> {
        match self {
            Type::Unknown => write!(ctx.out, "UNKNOWN"),
            Type::PrimitiveType(ptype) => write!(ctx.out, "{ptype}"),
            Type::Ptr(mutability, pointee) => {
                write!(ctx.out, "*{}", mutability.prefix_str())?;

                pointee.try_dump(ctx, extra)?;

                Ok(())
            }
            Type::Funptr(params, ret) => {
                write!(ctx.out, "*fun({}) ->", join_pretty(params, extra))?;

                ret.try_dump(ctx, extra)?;

                Ok(())
            }
            Type::Tmp(tmp) => {
                write!(ctx.out, "{tmp}")
            }
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

impl Display for PrimitiveType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            PrimitiveType::Isz => write!(f, "isz"),
            PrimitiveType::I128 => write!(f, "i128"),
            PrimitiveType::I64 => write!(f, "i64"),
            PrimitiveType::I32 => write!(f, "i32"),
            PrimitiveType::I16 => write!(f, "i16"),
            PrimitiveType::I8 => write!(f, "i8"),
            PrimitiveType::Usz => write!(f, "usz"),
            PrimitiveType::U128 => write!(f, "u128"),
            PrimitiveType::U64 => write!(f, "u64"),
            PrimitiveType::U32 => write!(f, "u32"),
            PrimitiveType::U16 => write!(f, "u16"),
            PrimitiveType::U8 => write!(f, "u8"),
            PrimitiveType::F128 => write!(f, "f128"),
            PrimitiveType::F64 => write!(f, "f64"),
            PrimitiveType::F32 => write!(f, "f32"),
            PrimitiveType::F16 => write!(f, "f16"),
            PrimitiveType::Bool => write!(f, "bool"),
            PrimitiveType::Str => write!(f, "str"),
            PrimitiveType::Char => write!(f, "char"),
            PrimitiveType::Never => write!(f, "never"),
            PrimitiveType::Void => write!(f, "void"),
            PrimitiveType::Type => write!(f, "type"),
        }
    }
}

impl PrettyDump<OrbDumper> for Binding {
    fn try_dump(&self, ctx: &mut PrettyCtxt, extra: &OrbDumper) -> io::Result<()> {
        let Binding {
            comptime,
            mutability,
            name,
            typ,
            loc,
        } = self;

        ctx.write_indent()?;

        write!(
            ctx.out,
            "{comptime}{mutability}{name}: ",
            comptime = comptime.prefix_str(),
            mutability = mutability.prefix_str(),
        )?;

        typ.try_dump(ctx, extra)?;

        writeln!(ctx.out, "; // -> {}", loc)?;

        Ok(())
    }
}

impl PrettyDump<OrbDumper> for Temporary {
    fn try_dump(&self, ctx: &mut PrettyCtxt, extra: &OrbDumper) -> io::Result<()> {
        let Temporary { comptime, id, typ } = self;

        ctx.write_indent()?;

        write!(
            ctx.out,
            "{comptime}tmp {name}: ",
            comptime = comptime.prefix_str(),
            name = id
        )?;

        typ.try_dump(ctx, extra)?;

        writeln!(ctx.out, ";")?;

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
            PValue::Binding(id) => extra.access_bindings(*id, |binding| -> io::Result<()> {
                write!(ctx.out, "{}", binding.name)?;

                Ok(())
            }),
            PValue::Tmp(tmp) => {
                write!(ctx.out, "{tmp}")
            }
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
            RValue::Uint(int) => int.write_as_string_unsigned(&mut ctx.out),
            RValue::Sint(int) => int.write_as_string_signed(&mut ctx.out),
            RValue::Float(float) => float.write(&mut ctx.out),
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
