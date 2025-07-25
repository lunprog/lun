//! Pretty printing for SCIR.
use std::io;

use lunc_utils::pretty::{PrettyCtxt, PrettyDump};

use crate::{ScArg, ScBlock, ScExpr, ScExpression, ScItem, ScModule, ScStatement, ScStmt};

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
        }
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

impl PrettyDump for ScExpr {
    fn try_dump(&self, ctx: &mut PrettyCtxt) -> io::Result<()> {
        let out = &mut ctx.out;

        match self {
            ScExpr::IntLit(i) => write!(out, "integer {i}"),
            ScExpr::BoolLit(b) => write!(out, "boolean {b}"),
            ScExpr::StringLit(s) => write!(out, "string {s:?}"),
            ScExpr::CharLit(c) => write!(out, "character {c:?}"),
            ScExpr::FloatLit(f) => write!(out, "float {f:.}"),
            ScExpr::Ident(sym) => sym.try_dump(ctx),
            ScExpr::Binary { lhs, op, rhs } => {
                ctx.pretty_struct("Binary")
                    .field("lhs", lhs)
                    .field("op", op)
                    .field("rhs", rhs)
                    .finish()?;

                Ok(())
            }
            ScExpr::Unary { op, expr } => {
                ctx.pretty_struct("Unary")
                    .field("op", op)
                    .field("expr", expr)
                    .finish()?;

                Ok(())
            }
            ScExpr::AddressOf { mutable, expr } => {
                ctx.pretty_struct("AddressOf")
                    .field("mutable", mutable)
                    .field("expr", expr)
                    .finish()?;

                Ok(())
            }
            ScExpr::FunCall { callee, args } => {
                ctx.pretty_struct("FunCall")
                    .field("callee", callee)
                    .field("args", args.as_slice())
                    .finish()?;

                Ok(())
            }
            ScExpr::If {
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
            ScExpr::Block { label, block } => {
                ctx.pretty_struct("Block")
                    .field("label", label)
                    .field("block", block)
                    .finish()?;

                Ok(())
            }
            ScExpr::Loop { label, body } => {
                ctx.pretty_struct("Loop")
                    .field("label", label)
                    .field("body", body)
                    .finish()?;

                Ok(())
            }
            ScExpr::Return { expr } => {
                ctx.pretty_struct("Return").field("expr", expr).finish()?;
                Ok(())
            }
            ScExpr::Break { label, expr } => {
                ctx.pretty_struct("Break")
                    .field("label", label)
                    .field("expr", expr)
                    .finish()?;
                Ok(())
            }
            ScExpr::Continue { label } => {
                if label.is_some() {
                    ctx.pretty_struct("Continue").field("label", label).finish()
                } else {
                    write!(ctx.out, "Continue")
                }
            }
            ScExpr::Null => {
                write!(ctx.out, "Null")
            }
            ScExpr::MemberAccess { expr, member } => {
                ctx.pretty_struct("MemberAccess")
                    .field("expr", expr)
                    .field("member", member)
                    .finish()?;

                Ok(())
            }
            ScExpr::QualifiedPath { path, sym } => {
                ctx.pretty_struct("QualifiedPath")
                    .field("path", path)
                    .field("sym", sym)
                    .finish()?;

                Ok(())
            }
            ScExpr::Underscore => write!(ctx.out, "Underscore"),
            ScExpr::FunDefinition {
                args,
                rettypexpr,
                body,
            } => {
                ctx.pretty_struct("FunDefinition")
                    .field("args", args.as_slice())
                    .field("rettypexpr", rettypexpr)
                    .field("body", body)
                    .finish()?;

                Ok(())
            }
            ScExpr::PointerType { mutable, typexpr } => {
                ctx.pretty_struct("PointerType")
                    .field("mutable", mutable)
                    .field("typexpr", typexpr)
                    .finish()?;

                Ok(())
            }
            ScExpr::FunPtrType { args, ret } => {
                ctx.pretty_struct("FunPtrType")
                    .field("args", args.as_slice())
                    .field("ret", ret)
                    .finish()?;

                Ok(())
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
