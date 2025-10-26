//! Pretty AST tree printer

use std::io::{self, Write};

use lunc_utils::{
    pretty::{PrettyCtxt, PrettyDump},
    pretty_struct,
};

use crate::{
    directive::Directive,
    expr::{Arg, Else, ExprKind, Expression, IfExpression},
    item::{Item, Module},
    stmt::{Block, Statement, StmtKind},
};

impl<E: Clone> PrettyDump<E> for Module {
    fn try_dump(&self, ctx: &mut PrettyCtxt, extra: &E) -> io::Result<()> {
        self.items.as_slice().try_dump(ctx, extra)
    }
}

impl<E: Clone> PrettyDump<E> for Item {
    fn try_dump(&self, ctx: &mut PrettyCtxt, extra: &E) -> io::Result<()> {
        match self {
            Item::GlobalDef {
                name,
                mutability,
                typeexpr,
                value,
                loc,
            } => {
                pretty_struct! (
                    ctx,
                    extra,
                    "GlobalDef",
                    {
                        name,
                        mutability,
                        typeexpr,
                        value,
                    },
                    loc
                );

                Ok(())
            }
            Item::GlobalUninit {
                name,
                typeexpr,
                loc,
            } => {
                pretty_struct! (
                    ctx,
                    extra,
                    "GlobalUninit",
                    {
                        name,
                        typeexpr,
                    },
                    loc
                );

                Ok(())
            }
            Item::ExternBlock { abi, items, loc } => {
                pretty_struct! (
                    ctx,
                    extra,
                    "ExternBlock",
                    {
                        abi,
                        items,
                    },
                    loc
                );

                Ok(())
            }
            Item::Directive(directive) => directive.try_dump(ctx, extra),
        }
    }
}

impl<E: Clone> PrettyDump<E> for Expression {
    fn try_dump(&self, ctx: &mut PrettyCtxt, extra: &E) -> io::Result<()> {
        self.kind.try_dump(ctx, extra)?;
        ctx.print_loc(&self.loc)?;
        Ok(())
    }
}

impl<E: Clone> PrettyDump<E> for ExprKind {
    fn try_dump(&self, ctx: &mut PrettyCtxt, extra: &E) -> io::Result<()> {
        let out = &mut ctx.out;
        match self {
            ExprKind::Lit(lit) => write!(out, "{lit}"),
            ExprKind::BoolLit(b) => write!(out, "boolean {b}"),
            ExprKind::Paren(expr) => {
                pretty_struct! (
                    ctx,
                    extra,
                    "Paren",
                    {
                        expr,
                    },
                );

                Ok(())
            }
            ExprKind::Path(path) => write!(out, "path {path}"),
            ExprKind::Binary { lhs, op, rhs } => {
                pretty_struct! (
                    ctx,
                    extra,
                    "Binary",
                    {
                        lhs,
                        op,
                        rhs,
                    },
                );

                Ok(())
            }
            ExprKind::Unary { op, expr } => {
                pretty_struct! (
                    ctx,
                    extra,
                    "Unary",
                    {
                        op,
                        expr,
                    },
                );

                Ok(())
            }
            ExprKind::Borrow(mutability, expr) => {
                pretty_struct! (
                    ctx,
                    extra,
                    "Borrow",
                    {
                        mutability,
                        expr,
                    },
                );

                Ok(())
            }
            ExprKind::Call { callee, args } => {
                pretty_struct! (
                    ctx,
                    extra,
                    "Call",
                    {
                        callee,
                        args,
                    },
                );

                Ok(())
            }
            ExprKind::If(ifexpr) => ifexpr.try_dump(ctx, extra),
            ExprKind::IfThenElse {
                cond,
                true_val,
                false_val,
            } => {
                pretty_struct! (
                    ctx,
                    extra,
                    "IfThenElse",
                    {
                        cond,
                        true_val,
                        false_val,
                    },
                );

                Ok(())
            }
            ExprKind::Block(block) => {
                block.try_dump(ctx, extra)?;

                Ok(())
            }
            ExprKind::BlockWithLabel { label, block } => {
                pretty_struct! (
                    ctx,
                    extra,
                    "LabeledBlock",
                    {
                        label,
                        block,
                    },
                );

                Ok(())
            }
            ExprKind::PredicateLoop { label, cond, body } => {
                pretty_struct! (
                    ctx,
                    extra,
                    "PredicateLoop",
                    {
                        label,
                        cond,
                        body,
                    },
                );

                Ok(())
            }
            ExprKind::IteratorLoop {
                label,
                variable,
                iterator,
                body,
                loc: _,
            } => {
                pretty_struct! (
                    ctx,
                    extra,
                    "IteratorLoop",
                    {
                        label,
                        variable,
                        iterator,
                        body
                    },
                );

                Ok(())
            }
            ExprKind::InfiniteLoop { label, body } => {
                pretty_struct! (
                    ctx,
                    extra,
                    "InfiniteLoop",
                    {
                        label,
                        body
                    },
                );

                Ok(())
            }
            ExprKind::Return { expr } => {
                pretty_struct! (
                    ctx,
                    extra,
                    "Return",
                    {
                        expr,
                    },
                );

                Ok(())
            }
            ExprKind::Break { label, expr } => {
                pretty_struct! (
                    ctx,
                    extra,
                    "Break",
                    {
                        label,
                        expr,
                    },
                );

                Ok(())
            }
            ExprKind::Continue { label } => {
                if label.is_some() {
                    pretty_struct! (
                        ctx,
                        extra,
                        "Continue",
                        {
                            label,
                        },
                    );
                    Ok(())
                } else {
                    write!(ctx.out, "Continue")
                }
            }
            ExprKind::Null => {
                write!(ctx.out, "Null")
            }
            ExprKind::Field { expr, member } => {
                pretty_struct! (
                    ctx,
                    extra,
                    "Field",
                    {
                        expr,
                        member,
                    },
                );

                Ok(())
            }
            ExprKind::FunDefinition {
                args,
                rettypeexpr,
                body,
            } => {
                pretty_struct! (
                    ctx,
                    extra,
                    "FunDefinition",
                    {
                        args,
                        rettypeexpr,
                        body,
                    },
                );

                Ok(())
            }
            ExprKind::FunDeclaration { args, rettypeexpr } => {
                pretty_struct! (
                    ctx,
                    extra,
                    "FunDeclaration",
                    {
                        args,
                        rettypeexpr,
                    },
                );

                Ok(())
            }
            ExprKind::PointerType(mutability, typeexpr) => {
                pretty_struct! (
                    ctx,
                    extra,
                    "PointerType",
                    {
                        mutability,
                        typeexpr,
                    },
                );

                Ok(())
            }
            ExprKind::FunPtrType { args, ret } => {
                pretty_struct! (
                    ctx,
                    extra,
                    "FunPtrType",
                    {
                        args,
                        ret,
                    },
                );

                Ok(())
            }
        }
    }
}

impl<E: Clone> PrettyDump<E> for Arg {
    fn try_dump(&self, ctx: &mut PrettyCtxt, extra: &E) -> io::Result<()> {
        let Arg {
            name,
            typeexpr,
            loc,
        } = self;

        pretty_struct! (
            ctx,
            extra,
            "Arg",
            {
                name,
                typeexpr,
            },
            loc
        );

        Ok(())
    }
}

impl<E: Clone> PrettyDump<E> for IfExpression {
    fn try_dump(&self, ctx: &mut PrettyCtxt, extra: &E) -> io::Result<()> {
        let IfExpression {
            cond,
            body,
            else_br,
            loc,
        } = &self;

        pretty_struct! (
            ctx,
            extra,
            "If",
            {
                cond,
                body,
                else_br,
            },
            loc
        );

        Ok(())
    }
}

impl<E: Clone> PrettyDump<E> for Block {
    fn try_dump(&self, ctx: &mut PrettyCtxt, extra: &E) -> io::Result<()> {
        struct LastExpr<'a>(&'a Option<Box<Expression>>);

        impl<'a, E: Clone> PrettyDump<E> for LastExpr<'a> {
            fn try_dump(&self, ctx: &mut PrettyCtxt, extra: &E) -> io::Result<()> {
                write!(ctx.out, "@last_expr: ")?;
                self.0.try_dump(ctx, extra)?;

                Ok(())
            }
        }

        let last = LastExpr(&self.last_expr);

        ctx.pretty_list(Some("Block".to_string()), extra)
            .items(self.stmts.iter())
            .item(last)
            .finish()?;

        ctx.print_loc(&self.loc)?;

        Ok(())
    }
}

impl<E: Clone> PrettyDump<E> for Statement {
    fn try_dump(&self, ctx: &mut PrettyCtxt, extra: &E) -> io::Result<()> {
        self.stmt.try_dump(ctx, extra)?;
        ctx.print_loc(&self.loc)?;
        Ok(())
    }
}

impl<E: Clone> PrettyDump<E> for StmtKind {
    fn try_dump(&self, ctx: &mut PrettyCtxt, extra: &E) -> io::Result<()> {
        match self {
            StmtKind::BindingDef {
                name,
                mutability,
                typeexpr,
                value,
            } => {
                pretty_struct! (
                    ctx,
                    extra,
                    "BindingDef",
                    {
                        name,
                        mutability,
                        typeexpr,
                        value,
                    },
                );

                Ok(())
            }
            StmtKind::Defer { expr } => {
                pretty_struct! (
                    ctx,
                    extra,
                    "Defer",
                    {
                        expr,
                    },
                );
                Ok(())
            }
            StmtKind::Expression(expr) => {
                expr.try_dump(ctx, extra)?;
                Ok(())
            }
        }
    }
}

impl<E: Clone> PrettyDump<E> for Else {
    fn try_dump(&self, ctx: &mut PrettyCtxt, extra: &E) -> io::Result<()> {
        match self {
            Else::IfExpr(ifexpr) => ifexpr.try_dump(ctx, extra),
            Else::Block(block) => block.try_dump(ctx, extra),
        }
    }
}

impl<E> PrettyDump<E> for Directive {
    fn try_dump(&self, ctx: &mut PrettyCtxt, extra: &E) -> io::Result<()> {
        match self {
            Directive::Mod { name, loc } => {
                pretty_struct! (
                    ctx,
                    extra,
                    "Directive:Mod",
                    {
                        name,
                    },
                    loc
                );

                Ok(())
            }
            Directive::Import { path, alias, loc } => {
                pretty_struct! (
                    ctx,
                    extra,
                    "Directive:Import",
                    {
                        path,
                        alias,
                    },
                    loc
                );

                Ok(())
            }
        }
    }
}
