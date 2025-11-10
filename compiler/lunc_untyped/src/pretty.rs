//! Pretty-printing for [UTIR](crate::utir).

use std::io::{self, Write};

use lunc_utils::{
    impl_pdump, join_display, join_pretty,
    pretty::{PrettyCtxt, PrettyDump},
    pretty_struct,
};

use crate::utir::*;

/// Struct used to [`PrettyDump`] SIR.
///
/// # Note
///
/// It can only be created by `PrettyDump` implementation of `Orb`.
#[derive(Debug, Clone)]
pub struct OrbDumper(());

impl<E> PrettyDump<E> for Orb {
    fn try_dump(&self, ctx: &mut PrettyCtxt, _: &E) -> io::Result<()> {
        let Orb { items } = self;

        let dumper = OrbDumper(());

        ctx.pretty_map(items.full_iter(), &dumper)?;

        Ok(())
    }
}

impl PrettyDump<OrbDumper> for Item {
    fn try_dump(&self, ctx: &mut PrettyCtxt, extra: &OrbDumper) -> io::Result<()> {
        match self {
            Self::Fundef(fundef) => fundef.try_dump(ctx, extra),
            Self::Fundecl(fundecl) => fundecl.try_dump(ctx, extra),
            Self::GlobalDef(globaldef) => globaldef.try_dump(ctx, extra),
            Self::GlobalUninit(globaluninit) => globaluninit.try_dump(ctx, extra),
            Self::Module(module) => module.try_dump(ctx, extra),
            Self::ExternBlock(externblock) => externblock.try_dump(ctx, extra),
        }
    }
}

impl PrettyDump<OrbDumper> for Fundef {
    fn try_dump(&self, ctx: &mut PrettyCtxt, extra: &OrbDumper) -> io::Result<()> {
        let Fundef {
            name,
            typ,
            params,
            ret_ty,
            entry,
            body,
            loc,
        } = self;

        pretty_struct! (
            ctx,
            extra,
            "Fundef",
            {
                name: name,
                typ: typ,
                params: ctx.pretty_map(params.full_iter(), extra)?,
                ret_ty: ret_ty,
                entry: entry,
                body: body,
            },
            loc
        );

        Ok(())
    }
}

impl PrettyDump<OrbDumper> for Fundecl {
    fn try_dump(&self, ctx: &mut PrettyCtxt, extra: &OrbDumper) -> io::Result<()> {
        let Fundecl {
            name,
            typ,
            params,
            ret_ty,
            body,
            loc,
        } = self;

        pretty_struct! (
            ctx,
            extra,
            "Fundecl",
            {
                name,
                typ,
                params,
                ret_ty,
                body,
            },
            loc
        );

        Ok(())
    }
}

impl PrettyDump<OrbDumper> for GlobalDef {
    fn try_dump(&self, ctx: &mut PrettyCtxt, extra: &OrbDumper) -> io::Result<()> {
        let GlobalDef {
            name,
            mutability,
            typ,
            value,
            body,
            loc,
        } = self;

        pretty_struct! (
            ctx,
            extra,
            "Fundecl",
            {
                name,
                mutability,
                typ,
                value,
                body,
            },
            loc
        );

        Ok(())
    }
}

impl PrettyDump<OrbDumper> for GlobalUninit {
    fn try_dump(&self, ctx: &mut PrettyCtxt, extra: &OrbDumper) -> io::Result<()> {
        let GlobalUninit {
            name,
            typ,
            body,
            loc,
        } = self;

        pretty_struct! (
            ctx,
            extra,
            "Fundecl",
            {
                name,
                typ,
                body,
            },
            loc
        );

        Ok(())
    }
}

impl PrettyDump<OrbDumper> for Module {
    fn try_dump(&self, ctx: &mut PrettyCtxt, extra: &OrbDumper) -> io::Result<()> {
        let Module { name, items, loc } = self;

        pretty_struct! (
            ctx,
            extra,
            "Module",
            {
                name,
                items,
            },
            loc
        );

        Ok(())
    }
}

impl PrettyDump<OrbDumper> for ExternBlock {
    fn try_dump(&self, ctx: &mut PrettyCtxt, extra: &OrbDumper) -> io::Result<()> {
        let ExternBlock { abi, items, loc } = self;

        pretty_struct! (
            ctx,
            extra,
            "ExternBlock",
            {
                abi,
                items,
                loc,
            },
            loc
        );

        Ok(())
    }
}

impl_pdump! {
    ExprId,
    StmtId,
    ItemId,
    BlockId,
    LabelId,
    ParamId,
    BindingId,
    LabelKind,
    TyVar,
    Uty,
}

impl PrettyDump<OrbDumper> for Param {
    fn try_dump(&self, ctx: &mut PrettyCtxt, extra: &OrbDumper) -> io::Result<()> {
        let Param { name, typ, loc } = self;

        pretty_struct! (
            ctx,
            extra,
            "Param",
            {
                name,
                typ,
            },
            loc
        );

        Ok(())
    }
}

impl PrettyDump<OrbDumper> for Body {
    fn try_dump(&self, ctx: &mut PrettyCtxt, extra: &OrbDumper) -> io::Result<()> {
        let Body {
            labels,
            bindings,
            stmts,
            exprs,
            blocks,
            expr_t,
            type_vars,
            expr_locs,
            stmt_locs,
        } = self;

        pretty_struct! (
            ctx,
            extra,
            "Body",
            {
                labels: ctx.pretty_map(labels.full_iter(), extra)?,
                bindings: ctx.pretty_map(bindings.full_iter(), extra)?,
                stmts: ctx.pretty_map(stmts.full_iter(), extra)?,
                exprs: ctx.pretty_map(exprs.full_iter(), extra)?,
                blocks: ctx.pretty_map(blocks.full_iter(), extra)?,
                expr_t: ctx.pretty_map(expr_t.iter(), extra)?,
                type_vars: ctx.pretty_map(type_vars.full_iter(), extra)?,
                expr_locs: ctx.pretty_map(expr_locs.iter(), extra)?,
                stmt_locs: ctx.pretty_map(stmt_locs.iter(), extra)?,
            },
        );

        Ok(())
    }
}

impl PrettyDump<OrbDumper> for Stmt {
    fn try_dump(&self, ctx: &mut PrettyCtxt, extra: &OrbDumper) -> io::Result<()> {
        match self {
            Self::BindingDef(id) => id.try_dump(ctx, extra),
            Self::Expression(expr) => expr.try_dump(ctx, extra),
        }
    }
}

impl PrettyDump<OrbDumper> for Expr {
    fn try_dump(&self, ctx: &mut PrettyCtxt, extra: &OrbDumper) -> io::Result<()> {
        match self {
            Self::Int(i) => write!(ctx.out, "int({i})"),
            Self::Char(c) => write!(ctx.out, "char({c:?})"),
            Self::Float(f) => write!(ctx.out, "float({f})"),
            Self::Str(s) => write!(ctx.out, "str({s:?})"),
            Self::CStr(s) => write!(ctx.out, "cstr({s:?})"),
            Self::Bool(b) => write!(ctx.out, "bool({b})"),
            Self::Item(id) => id.try_dump(ctx, extra),
            Self::Param(ord) => write!(ctx.out, "param({ord})"),
            Self::Binding(id) => id.try_dump(ctx, extra),
            Self::Binary(lhs, op, rhs) => write!(ctx.out, "{lhs} {op} {rhs}"),
            Self::Unary(op, expr) => write!(ctx.out, "{op} {expr}"),
            Self::Borrow(mutability, expr) => write!(ctx.out, "&{}{expr}", mutability.prefix_str()),
            Self::Call { callee, args } => {
                write!(ctx.out, "call({callee}, ({}))", join_display(args))
            }
            Self::If {
                cond,
                then_e,
                else_e,
            } => {
                write!(ctx.out, "if {cond} {{ {then_e} }}")?;

                if let Some(else_e) = else_e.expand() {
                    write!(ctx.out, " else {{ {else_e} }}")?;
                }

                Ok(())
            }
            Self::Block(label, block) => {
                write!(ctx.out, "block({label}, {block})")
            }
            Self::Loop(label, block) => {
                write!(ctx.out, "loop {{{label}, {block}}}")
            }
            Self::Return(expr) => {
                write!(ctx.out, "return {expr}")
            }
            Self::Break(label, expr) => {
                write!(ctx.out, "break({label}, {expr})")
            }
            Self::Continue(label) => {
                write!(ctx.out, "continue({label})")
            }
            Self::Underscore => {
                write!(ctx.out, "underscore")
            }
            Self::PtrType(mutability, pointee) => {
                write!(ctx.out, "*{}{pointee}", mutability.prefix_str())
            }
            Self::FunptrType(params, ret) => {
                write!(ctx.out, "*fun({})", join_display(params))?;

                if let Some(ret) = ret.expand() {
                    write!(ctx.out, "-> {ret}")?;
                }

                Ok(())
            }
            Self::PrimType(ptype) => write!(ctx.out, "primitive_type({ptype})"),
        }
    }
}

impl PrettyDump<OrbDumper> for Block {
    fn try_dump(&self, ctx: &mut PrettyCtxt, extra: &OrbDumper) -> io::Result<()> {
        let Block {
            stmts,
            tail,
            typ,
            loc,
        } = self;

        pretty_struct! (
            ctx,
            extra,
            "Block",
            {
                stmts,
                tail,
                typ,
            },
            loc
        );

        Ok(())
    }
}

impl PrettyDump<OrbDumper> for Label {
    fn try_dump(&self, ctx: &mut PrettyCtxt, extra: &OrbDumper) -> io::Result<()> {
        let Label {
            id: _, // already printed
            name,
            typ,
            kind,
        } = self;

        pretty_struct! (
            ctx,
            extra,
            "Label",
            {
                name,
                typ,
                kind,
            }
        );

        Ok(())
    }
}

impl PrettyDump<OrbDumper> for BindingDef {
    fn try_dump(&self, ctx: &mut PrettyCtxt, extra: &OrbDumper) -> io::Result<()> {
        let BindingDef {
            name,
            mutability,
            typ,
            val,
        } = self;

        pretty_struct! (
            ctx,
            extra,
            "BindingDef",
            {
                name,
                mutability,
                typ,
                val,
            }
        );

        Ok(())
    }
}

impl PrettyDump<OrbDumper> for Con {
    fn try_dump(&self, ctx: &mut PrettyCtxt, _: &OrbDumper) -> io::Result<()> {
        match self {
            Con::Integer(tyvar) => write!(ctx.out, "{tyvar} = integer"),
            Con::Float(tyvar) => write!(ctx.out, "{tyvar} = float"),
            Con::Uty(tyvar, ty) => write!(ctx.out, "{tyvar} = {ty}"),
        }
    }
}

impl PrettyDump<OrbDumper> for Constraints {
    fn try_dump(&self, ctx: &mut PrettyCtxt, extra: &OrbDumper) -> io::Result<()> {
        let Constraints(cons) = self;

        write!(ctx.out, "{{{}}}", join_pretty(cons, extra))
    }
}
