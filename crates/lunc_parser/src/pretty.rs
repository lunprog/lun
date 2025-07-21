//! Pretty AST tree printer

use std::io;

use lunc_utils::pretty::{PrettyCtxt, PrettyDump};

use crate::{
    directive::{EffectivePath, ItemDirective, QualifiedPath},
    expr::{Arg, BinOp, Else, Expr, Expression, IfExpression, UnaryOp},
    item::{Item, Module},
    stmt::{Block, Statement, Stmt},
};

impl PrettyDump for Module {
    fn try_dump(&self, ctx: &mut PrettyCtxt) -> io::Result<()> {
        self.items.as_slice().try_dump(ctx)
    }
}

impl PrettyDump for Item {
    fn try_dump(&self, ctx: &mut PrettyCtxt) -> io::Result<()> {
        match self {
            Item::GlobalConst {
                name,
                name_loc,
                typ,
                value,
                loc,
            } => {
                ctx.pretty_struct("GlobalConst")
                    .field("name", (name, name_loc))
                    .field("typ", typ)
                    .field("value", value)
                    .finish()?;
                ctx.print_loc(loc)?;

                Ok(())
            }
            Item::GlobalVar {
                name,
                name_loc,
                typ,
                value,
                loc,
            } => {
                ctx.pretty_struct("GlobalVar")
                    .field("name", (name, name_loc))
                    .field("typ", typ)
                    .field("value", value)
                    .finish()?;
                ctx.print_loc(loc)?;

                Ok(())
            }
            Item::Directive(directive) => directive.try_dump(ctx),
        }
    }
}

impl PrettyDump for Expression {
    fn try_dump(&self, ctx: &mut PrettyCtxt) -> io::Result<()> {
        self.expr.try_dump(ctx)?;
        ctx.print_loc(&self.loc)?;
        Ok(())
    }
}

impl PrettyDump for Expr {
    fn try_dump(&self, ctx: &mut PrettyCtxt) -> io::Result<()> {
        let out = &mut ctx.out;
        match self {
            Expr::IntLit(i) => write!(out, "integer {i}"),
            Expr::BoolLit(b) => write!(out, "boolean {b}"),
            Expr::StringLit(s) => write!(out, "string {s:?}"),
            Expr::CharLit(c) => write!(out, "character {c:?}"),
            Expr::FloatLit(f) => write!(out, "float {f:.}"),
            Expr::Grouping(e) => {
                ctx.pretty_struct("Grouping").field("expr", e).finish()?;

                Ok(())
            }
            Expr::Ident(id) => write!(out, "ident {id}"),
            Expr::Binary { lhs, op, rhs } => {
                ctx.pretty_struct("Binary")
                    .field("lhs", lhs)
                    .field("op", op)
                    .field("rhs", rhs)
                    .finish()?;

                Ok(())
            }
            Expr::Unary { op, expr } => {
                ctx.pretty_struct("Unary")
                    .field("op", op)
                    .field("expr", expr)
                    .finish()?;

                Ok(())
            }
            Expr::AddressOf { mutable, expr } => {
                ctx.pretty_struct("AddressOf")
                    .field("mutable", mutable)
                    .field("expr", expr)
                    .finish()?;

                Ok(())
            }
            Expr::FunCall { callee, args } => {
                ctx.pretty_struct("FunCall")
                    .field("callee", callee)
                    .field("args", args.as_slice())
                    .finish()?;

                Ok(())
            }
            Expr::If(ifexpr) => ifexpr.try_dump(ctx),
            Expr::IfThenElse {
                cond,
                true_val,
                false_val,
            } => {
                ctx.pretty_struct("IfThenElse")
                    .field("cond", cond)
                    .field("true_val", true_val)
                    .field("false_val", false_val)
                    .finish()?;

                Ok(())
            }
            Expr::Block(block) => {
                write!(ctx.out, "Block ")?;
                block.try_dump(ctx)?;

                Ok(())
            }
            Expr::BlockWithLabel { label, block } => {
                ctx.pretty_struct("BlockWithLabel")
                    .field("label", label)
                    .field("block", block)
                    .finish()?;

                Ok(())
            }
            Expr::PredicateLoop { label, cond, body } => {
                ctx.pretty_struct("PredicateLoop")
                    .field("label", label)
                    .field("cond", cond)
                    .field("body", body)
                    .finish()?;

                Ok(())
            }
            Expr::IteratorLoop {
                label,
                variable,
                iterator,
                body,
            } => {
                ctx.pretty_struct("IteratorLoop")
                    .field("label", label)
                    .field("variable", variable)
                    .field("iterator", iterator)
                    .field("body", body)
                    .finish()?;

                Ok(())
            }
            Expr::InfiniteLoop { label, body } => {
                ctx.pretty_struct("InfiniteLoop")
                    .field("label", label)
                    .field("body", body)
                    .finish()?;

                Ok(())
            }
            Expr::Return { expr } => {
                ctx.pretty_struct("Return").field("expr", expr).finish()?;
                Ok(())
            }
            Expr::Break { label, expr } => {
                ctx.pretty_struct("Break")
                    .field("label", label)
                    .field("expr", expr)
                    .finish()?;

                Ok(())
            }
            Expr::Continue { label } => {
                if label.is_some() {
                    ctx.pretty_struct("Continue").field("label", label).finish()
                } else {
                    write!(ctx.out, "Continue")
                }
            }
            Expr::Null => {
                write!(ctx.out, "Null")
            }
            Expr::MemberAccess { expr, member } => {
                ctx.pretty_struct("MemberAccess")
                    .field("expr", expr)
                    .field("member", member)
                    .finish()?;

                Ok(())
            }
            Expr::Orb => {
                write!(ctx.out, "Orb")
            }
            Expr::FunDefinition {
                args,
                rettype,
                body,
            } => {
                ctx.pretty_struct("FunDefinition")
                    .field("args", args.as_slice())
                    .field("rettype", rettype)
                    .field("body", body)
                    .finish()?;

                Ok(())
            }
            Expr::PointerType { mutable, typ } => {
                ctx.pretty_struct("PointerType")
                    .field("mutable", mutable)
                    .field("typ", typ)
                    .finish()?;

                Ok(())
            }
            Expr::FunPtrType { args, ret } => {
                ctx.pretty_struct("FunPtrType")
                    .field("args", args.as_slice())
                    .field("ret", ret)
                    .finish()?;

                Ok(())
            }
        }
    }
}

impl PrettyDump for Arg {
    fn try_dump(&self, ctx: &mut PrettyCtxt) -> io::Result<()> {
        let Arg {
            name,
            name_loc,
            typ,
            loc,
        } = self;

        ctx.pretty_struct("Arg")
            .field("name", (name, name_loc))
            .field("typ", typ)
            .finish()?;
        ctx.print_loc(loc)?;

        Ok(())
    }
}

impl PrettyDump for IfExpression {
    fn try_dump(&self, ctx: &mut PrettyCtxt) -> io::Result<()> {
        let IfExpression {
            cond,
            body,
            else_br,
            loc,
        } = &self;

        ctx.pretty_struct("If")
            .field("cond", cond)
            .field("body", body)
            .field("else_br", else_br)
            .finish()?;

        ctx.print_loc(loc)?;
        Ok(())
    }
}

impl PrettyDump for BinOp {
    fn try_dump(&self, ctx: &mut PrettyCtxt) -> io::Result<()> {
        write!(ctx.out, "{self:?}")
    }
}

impl PrettyDump for UnaryOp {
    fn try_dump(&self, ctx: &mut PrettyCtxt) -> io::Result<()> {
        write!(ctx.out, "{self:?}")
    }
}

impl PrettyDump for Block {
    fn try_dump(&self, ctx: &mut PrettyCtxt) -> io::Result<()> {
        struct LastExpr<'a>(&'a Option<Box<Expression>>);

        impl<'a> PrettyDump for LastExpr<'a> {
            fn try_dump(&self, ctx: &mut PrettyCtxt) -> io::Result<()> {
                write!(ctx.out, "@last_expr: ")?;
                self.0.try_dump(ctx)?;

                Ok(())
            }
        }

        let last = LastExpr(&self.last_expr);

        ctx.pretty_list()
            .items(self.stmts.iter())
            .items(last.0.iter())
            .finish()?;

        ctx.print_loc(&self.loc)?;

        Ok(())
    }
}

impl PrettyDump for Statement {
    fn try_dump(&self, ctx: &mut PrettyCtxt) -> io::Result<()> {
        self.stmt.try_dump(ctx)?;
        ctx.print_loc(&self.loc)?;
        Ok(())
    }
}

impl PrettyDump for Stmt {
    fn try_dump(&self, ctx: &mut PrettyCtxt) -> io::Result<()> {
        match self {
            Stmt::VariableDef {
                name,
                name_loc,
                mutable,
                typ,
                value,
            } => {
                ctx.pretty_struct("VariableDef")
                    .field("name", (name, name_loc))
                    .field("mutable", mutable)
                    .field("typ", typ)
                    .field("value", value)
                    .finish()?;
                Ok(())
            }
            Stmt::Defer { expr } => {
                ctx.pretty_struct("Defer").field("expr", expr).finish()?;
                Ok(())
            }
            Stmt::Expression(expr) => {
                expr.try_dump(ctx)?;
                Ok(())
            }
        }
    }
}

impl PrettyDump for Else {
    fn try_dump(&self, ctx: &mut PrettyCtxt) -> io::Result<()> {
        match self {
            Else::IfExpr(ifexpr) => ifexpr.try_dump(ctx),
            Else::Block(block) => block.try_dump(ctx),
        }
    }
}

impl PrettyDump for ItemDirective {
    fn try_dump(&self, ctx: &mut PrettyCtxt) -> io::Result<()> {
        match self {
            ItemDirective::Mod { name, loc } => {
                ctx.pretty_struct("Mod").field("name", name).finish()?;
                ctx.print_loc(loc)?;

                Ok(())
            }
            ItemDirective::Use { path, alias, loc } => {
                ctx.pretty_struct("Use")
                    .field("path", path)
                    .field("alias", alias)
                    .finish()?;

                ctx.print_loc(loc)?;

                Ok(())
            }
        }
    }
}

impl PrettyDump for EffectivePath {
    fn try_dump(&self, ctx: &mut PrettyCtxt) -> io::Result<()> {
        write!(ctx.out, "{self}")
    }
}

impl PrettyDump for QualifiedPath {
    fn try_dump(&self, ctx: &mut PrettyCtxt) -> io::Result<()> {
        let QualifiedPath { path, loc } = self;

        path.try_dump(ctx)?;
        ctx.print_loc(loc)
    }
}
