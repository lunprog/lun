//! Pretty printing for SCIR.

use std::io::{self, Write};

use lunc_utils::{
    Span,
    pretty::{PrettyCtxt, PrettyDump},
};

use crate::{
    FunDefInfo, ScArg, ScBlock, ScExprKind, ScExpression, ScItem, ScModule, ScStatement, ScStmt,
};

impl PrettyDump for ScModule {
    fn try_dump(&self, ctx: &mut PrettyCtxt) -> io::Result<()> {
        self.items.as_slice().try_dump(ctx)
    }
}

impl PrettyDump for ScItem {
    fn try_dump(&self, ctx: &mut PrettyCtxt) -> io::Result<()> {
        match self {
            ScItem::GlobalDef {
                name,
                name_loc,
                mutable,
                typexpr,
                value,
                loc,
                sym,
            } => {
                ctx.pretty_struct("GlobalDef")
                    .field("name", (name, name_loc))
                    .field("mutable", mutable)
                    .field("typexpr", typexpr)
                    .field("value", value)
                    .field("sym", sym)
                    .finish()?;

                ctx.print_loc(loc)?;

                Ok(())
            }
            ScItem::GlobalUninit {
                name,
                name_loc,
                typexpr,
                loc,
                sym,
            } => {
                ctx.pretty_struct("GlobalUninit")
                    .field("name", (name, name_loc))
                    .field("typexpr", typexpr)
                    .field("sym", sym)
                    .finish()?;

                ctx.print_loc(loc)?;

                Ok(())
            }
            ScItem::FunDefinition {
                name,
                name_loc,
                typexpr,
                args,
                rettypexpr,
                body,
                info,
                loc,
                sym,
            } => {
                ctx.pretty_struct("FunDefinition")
                    .field("name", (name, name_loc))
                    .field("typexpr", typexpr)
                    .field("args", args.as_slice())
                    .field("rettypexpr", rettypexpr)
                    .field("body", body)
                    .field("info", info)
                    .field("sym", sym)
                    .finish()?;

                ctx.print_loc(loc)?;

                Ok(())
            }
            ScItem::FunDeclaration {
                name,
                name_loc,
                typexpr,
                args,
                rettypexpr,
                defined_mut,
                loc,
                sym,
            } => {
                ctx.pretty_struct("FunDeclaration")
                    .field("name", (name, name_loc))
                    .field("typexpr", typexpr)
                    .field("args", args.as_slice())
                    .field("rettypexpr", rettypexpr)
                    .field("defined_mut", defined_mut)
                    .field("sym", sym)
                    .finish()?;
                ctx.print_loc(loc)?;

                Ok(())
            }
            ScItem::Module {
                name,
                module,
                loc,
                sym,
            } => {
                ctx.pretty_struct("Module")
                    .field("name", name)
                    .field("module", module)
                    .field("sym", sym)
                    .finish()?;

                ctx.print_loc(loc)?;

                Ok(())
            }
            ScItem::ExternBlock { abi, items, loc } => {
                ctx.pretty_struct("ExternBlock")
                    .field("abi", abi)
                    .field("items", items.as_slice())
                    .finish()?;

                ctx.print_loc(loc)?;

                Ok(())
            }
        }
    }
}

impl PrettyDump for FunDefInfo {
    fn try_dump(&self, ctx: &mut PrettyCtxt) -> io::Result<()> {
        let FunDefInfo { defined_mut } = self;

        ctx.pretty_struct("")
            .field("defined_mut", defined_mut)
            .finish()?;

        Ok(())
    }
}

impl PrettyDump for ScExpression {
    fn try_dump(&self, ctx: &mut PrettyCtxt) -> io::Result<()> {
        let ScExpression { expr, typ, loc } = self;

        ctx.pretty_struct("Expression")
            .field("expr", expr)
            .field("typ", typ)
            .finish()?;

        ctx.print_loc(loc)?;
        Ok(())
    }
}

impl PrettyDump for ScExprKind {
    fn try_dump(&self, ctx: &mut PrettyCtxt) -> io::Result<()> {
        let out = &mut ctx.out;

        match self {
            ScExprKind::Lit(lit) => write!(out, "{lit}"),
            ScExprKind::BoolLit(b) => write!(out, "boolean {b}"),
            ScExprKind::Ident(sym) => sym.try_dump(ctx),
            ScExprKind::Binary { lhs, op, rhs } => {
                ctx.pretty_struct("Binary")
                    .field("lhs", lhs)
                    .field("op", op)
                    .field("rhs", rhs)
                    .finish()?;

                Ok(())
            }
            ScExprKind::Unary { op, expr } => {
                ctx.pretty_struct("Unary")
                    .field("op", op)
                    .field("expr", expr)
                    .finish()?;

                Ok(())
            }
            ScExprKind::Borrow { mutable, expr } => {
                ctx.pretty_struct("Borrow")
                    .field("mutable", mutable)
                    .field("expr", expr)
                    .finish()?;

                Ok(())
            }
            ScExprKind::FunCall { callee, args } => {
                ctx.pretty_struct("FunCall")
                    .field("callee", callee)
                    .field("args", args.as_slice())
                    .finish()?;

                Ok(())
            }
            ScExprKind::If {
                cond,
                then_br,
                else_br,
            } => {
                ctx.pretty_struct("If")
                    .field("cond", cond)
                    .field("then_br", then_br)
                    .field("else_br", else_br)
                    .finish()?;

                Ok(())
            }
            ScExprKind::Block {
                label,
                block,
                index,
            } => {
                ctx.pretty_struct("Block")
                    .field(
                        "label",
                        (
                            label.clone().map(|l| l.0),
                            &label.clone().map(|l| l.1).unwrap_or(Span::ZERO),
                        ),
                    )
                    .field("block", block)
                    .field("index", index)
                    .finish()?;

                Ok(())
            }
            ScExprKind::Loop { label, body, index } => {
                ctx.pretty_struct("Loop")
                    .field(
                        "label",
                        (
                            label.clone().map(|l| l.0),
                            &label.clone().map(|l| l.1).unwrap_or(Span::ZERO),
                        ),
                    )
                    .field("body", body)
                    .field("index", index)
                    .finish()?;

                Ok(())
            }
            ScExprKind::Return { expr } => {
                ctx.pretty_struct("Return").field("expr", expr).finish()?;
                Ok(())
            }
            ScExprKind::Break { label, expr, index } => {
                ctx.pretty_struct("Break")
                    .field("label", label)
                    .field("expr", expr)
                    .field("index", index)
                    .finish()?;

                Ok(())
            }
            ScExprKind::Continue { label, index } => {
                ctx.pretty_struct("Continue")
                    .field("label", label)
                    .field("index", index)
                    .finish()?;

                Ok(())
            }
            ScExprKind::Null => {
                write!(ctx.out, "Null")
            }
            ScExprKind::Field { expr, member } => {
                ctx.pretty_struct("Field")
                    .field("expr", expr)
                    .field("member", member)
                    .finish()?;

                Ok(())
            }
            ScExprKind::QualifiedPath { path, sym } => {
                ctx.pretty_struct("QualifiedPath")
                    .field("path", path)
                    .field("sym", sym)
                    .finish()?;

                Ok(())
            }
            ScExprKind::Underscore => write!(ctx.out, "Underscore"),
            ScExprKind::PointerType { mutable, typexpr } => {
                ctx.pretty_struct("PointerType")
                    .field("mutable", mutable)
                    .field("typexpr", typexpr)
                    .finish()?;

                Ok(())
            }
            ScExprKind::FunPtrType { args, ret } => {
                ctx.pretty_struct("FunPtrType")
                    .field("args", args.as_slice())
                    .field("ret", ret)
                    .finish()?;

                Ok(())
            }
            ScExprKind::Poisoned { diag } => {
                write!(ctx.out, "POISONED: {diag:#?}")
            }
        }
    }
}

impl PrettyDump for ScArg {
    fn try_dump(&self, ctx: &mut PrettyCtxt) -> io::Result<()> {
        let ScArg {
            name,
            name_loc,
            typexpr,
            loc,
            sym,
        } = self;

        ctx.pretty_struct("Arg")
            .field("name", (name, name_loc))
            .field("typexpr", typexpr)
            .field("sym", sym)
            .finish()?;

        ctx.print_loc(loc)?;

        Ok(())
    }
}

impl PrettyDump for ScBlock {
    fn try_dump(&self, ctx: &mut PrettyCtxt) -> io::Result<()> {
        let ScBlock {
            stmts,
            last_expr,
            loc,
            typ,
        } = self;

        ctx.pretty_struct("Block")
            .field("stmts", stmts.as_slice())
            .field("last_expr", last_expr)
            .field("typ", typ)
            .finish()?;

        ctx.print_loc(loc)?;

        Ok(())
    }
}

impl PrettyDump for ScStatement {
    fn try_dump(&self, ctx: &mut PrettyCtxt) -> io::Result<()> {
        let ScStatement { stmt, loc } = self;

        stmt.try_dump(ctx)?;
        ctx.print_loc(loc)?;

        Ok(())
    }
}

impl PrettyDump for ScStmt {
    fn try_dump(&self, ctx: &mut PrettyCtxt) -> io::Result<()> {
        match self {
            ScStmt::VariableDef {
                name,
                name_loc,
                mutable,
                typexpr,
                value,
                sym,
            } => {
                ctx.pretty_struct("VariableDef")
                    .field("name", (name, name_loc))
                    .field("mutable", mutable)
                    .field("typexpr", typexpr)
                    .field("value", value)
                    .field("sym", sym)
                    .finish()?;

                Ok(())
            }
            ScStmt::Defer { expr } => {
                ctx.pretty_struct("Defer").field("expr", expr).finish()?;

                Ok(())
            }
            ScStmt::Expression(expr) => expr.try_dump(ctx),
        }
    }
}
