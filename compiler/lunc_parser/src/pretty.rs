//! Pretty AST tree printer

use std::io::{self, Write};

use lunc_utils::pretty::{PrettyCtxt, PrettyDump};

use crate::{
    directive::Directive,
    expr::{Arg, Else, ExprKind, Expression, IfExpression},
    item::{Item, Module},
    stmt::{Block, Statement, StmtKind},
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
                typexpr,
                value,
                loc,
            } => {
                ctx.pretty_struct("GlobalConst")
                    .field("name", (name, name_loc))
                    .field("typexpr", typexpr)
                    .field("value", value)
                    .finish()?;
                ctx.print_loc(loc)?;

                Ok(())
            }
            Item::GlobalVar {
                name,
                name_loc,
                typexpr,
                value,
                loc,
            } => {
                ctx.pretty_struct("GlobalVar")
                    .field("name", (name, name_loc))
                    .field("typexpr", typexpr)
                    .field("value", value)
                    .finish()?;
                ctx.print_loc(loc)?;

                Ok(())
            }
            Item::GlobalUninit {
                name,
                name_loc,
                typexpr,
                loc,
            } => {
                ctx.pretty_struct("GlobalUninit")
                    .field("name", (name, name_loc))
                    .field("typexpr", typexpr)
                    .finish()?;
                ctx.print_loc(loc)?;

                Ok(())
            }
            Item::ExternBlock { abi, items, loc } => {
                ctx.pretty_struct("ExternBlock")
                    .field("abi", abi)
                    .field("items", items.as_slice())
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
        self.kind.try_dump(ctx)?;
        ctx.print_loc(&self.loc)?;
        Ok(())
    }
}

impl PrettyDump for ExprKind {
    fn try_dump(&self, ctx: &mut PrettyCtxt) -> io::Result<()> {
        let out = &mut ctx.out;
        match self {
            ExprKind::Lit(lit) => write!(out, "{lit}"),
            ExprKind::BoolLit(b) => write!(out, "boolean {b}"),
            ExprKind::Paren(e) => {
                ctx.pretty_struct("Paren").field("expr", e).finish()?;

                Ok(())
            }
            ExprKind::Ident(id) => write!(out, "ident {id}"),
            // Expr::Path(path) => write!(out, "path {path}"),
            ExprKind::Binary { lhs, op, rhs } => {
                ctx.pretty_struct("Binary")
                    .field("lhs", lhs)
                    .field("op", op)
                    .field("rhs", rhs)
                    .finish()?;

                Ok(())
            }
            ExprKind::Unary { op, expr } => {
                ctx.pretty_struct("Unary")
                    .field("op", op)
                    .field("expr", expr)
                    .finish()?;

                Ok(())
            }
            ExprKind::Borrow(mutability, expr) => {
                ctx.pretty_struct("Borrow")
                    .field("mutability", mutability)
                    .field("expr", expr)
                    .finish()?;

                Ok(())
            }
            ExprKind::Call { callee, args } => {
                ctx.pretty_struct("Call")
                    .field("callee", callee)
                    .field("args", args.as_slice())
                    .finish()?;

                Ok(())
            }
            ExprKind::If(ifexpr) => ifexpr.try_dump(ctx),
            ExprKind::IfThenElse {
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
            ExprKind::Block(block) => {
                block.try_dump(ctx)?;

                Ok(())
            }
            ExprKind::BlockWithLabel { label, block } => {
                ctx.pretty_struct("BlockWithLabel")
                    .field("label", label)
                    .field("block", block)
                    .finish()?;

                Ok(())
            }
            ExprKind::PredicateLoop { label, cond, body } => {
                ctx.pretty_struct("PredicateLoop")
                    .field("label", label)
                    .field("cond", cond)
                    .field("body", body)
                    .finish()?;

                Ok(())
            }
            ExprKind::IteratorLoop {
                label,
                variable,
                iterator,
                body,
                loc: _,
            } => {
                ctx.pretty_struct("IteratorLoop")
                    .field("label", label)
                    .field("variable", variable)
                    .field("iterator", iterator)
                    .field("body", body)
                    .finish()?;

                Ok(())
            }
            ExprKind::InfiniteLoop { label, body } => {
                ctx.pretty_struct("InfiniteLoop")
                    .field("label", label)
                    .field("body", body)
                    .finish()?;

                Ok(())
            }
            ExprKind::Return { expr } => {
                ctx.pretty_struct("Return").field("expr", expr).finish()?;
                Ok(())
            }
            ExprKind::Break { label, expr } => {
                ctx.pretty_struct("Break")
                    .field("label", label)
                    .field("expr", expr)
                    .finish()?;

                Ok(())
            }
            ExprKind::Continue { label } => {
                if label.is_some() {
                    ctx.pretty_struct("Continue").field("label", label).finish()
                } else {
                    write!(ctx.out, "Continue")
                }
            }
            ExprKind::Null => {
                write!(ctx.out, "Null")
            }
            ExprKind::Field { expr, member } => {
                ctx.pretty_struct("Field")
                    .field("expr", expr)
                    .field("member", member)
                    .finish()?;

                Ok(())
            }
            ExprKind::Orb => {
                write!(ctx.out, "Orb")
            }
            ExprKind::FunDefinition {
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
            ExprKind::FunDeclaration { args, rettypexpr } => {
                ctx.pretty_struct("FunDeclaration")
                    .field("args", args.as_slice())
                    .field("rettypexpr ", rettypexpr)
                    .finish()?;

                Ok(())
            }
            ExprKind::PointerType(mutability, typexpr) => {
                ctx.pretty_struct("PointerType")
                    .field("mutability", mutability)
                    .field("typexpr", typexpr)
                    .finish()?;

                Ok(())
            }
            ExprKind::FunPtrType { args, ret } => {
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
            typexpr,
            loc,
        } = self;

        ctx.pretty_struct("Arg")
            .field("name", (name, name_loc))
            .field("typexpr", typexpr)
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

        ctx.pretty_list(Some("Block".to_string()))
            .items(self.stmts.iter())
            .item(last)
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

impl PrettyDump for StmtKind {
    fn try_dump(&self, ctx: &mut PrettyCtxt) -> io::Result<()> {
        match self {
            StmtKind::BindingDef {
                name,
                mutability,
                typexpr,
                value,
            } => {
                ctx.pretty_struct("BindingDef")
                    .field("name", name)
                    .field("mutability", mutability)
                    .field("typexpr", typexpr)
                    .field("value", value)
                    .finish()?;
                Ok(())
            }
            StmtKind::Defer { expr } => {
                ctx.pretty_struct("Defer").field("expr", expr).finish()?;
                Ok(())
            }
            StmtKind::Expression(expr) => {
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

impl PrettyDump for Directive {
    fn try_dump(&self, ctx: &mut PrettyCtxt) -> io::Result<()> {
        match self {
            Directive::Mod { name, loc } => {
                ctx.pretty_struct("Mod").field("name", name).finish()?;
                ctx.print_loc(loc)?;

                Ok(())
            }
            Directive::Import { path, alias, loc } => {
                ctx.pretty_struct("Import")
                    .field("path", path)
                    .field("alias", alias)
                    .finish()?;

                ctx.print_loc(loc)?;

                Ok(())
            }
        }
    }
}
