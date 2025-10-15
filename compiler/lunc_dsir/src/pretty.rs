//! Pretty printing for DSIR.

use std::io::{self, Write};

use lunc_utils::{
    Span,
    pretty::{PrettyCtxt, PrettyDump},
};

use crate::{
    DsArg, DsBlock, DsDirective, DsExprKind, DsExpression, DsItem, DsModule, DsStatement, DsStmt,
};

impl PrettyDump for DsModule {
    fn try_dump(&self, ctx: &mut PrettyCtxt) -> io::Result<()> {
        self.items.as_slice().try_dump(ctx)
    }
}

impl PrettyDump for DsItem {
    fn try_dump(&self, ctx: &mut PrettyCtxt) -> io::Result<()> {
        match self {
            DsItem::GlobalDef {
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
            DsItem::GlobalUninit {
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
            DsItem::Module {
                name,
                module,
                loc,
                sym,
            } => {
                ctx.pretty_struct("Module")
                    .field("name", (name, loc))
                    .field("module", module)
                    .field("sym", sym)
                    .finish()?;

                Ok(())
            }
            DsItem::ExternBlock { abi, items, loc } => {
                ctx.pretty_struct("ExternBlock")
                    .field("abi", abi)
                    .field("items", items.as_slice())
                    .finish()?;

                ctx.print_loc(loc)?;

                Ok(())
            }
            DsItem::Directive(directive) => directive.try_dump(ctx),
        }
    }
}

impl PrettyDump for DsDirective {
    fn try_dump(&self, ctx: &mut PrettyCtxt) -> io::Result<()> {
        match self {
            Self::Import { path, alias, loc } => {
                ctx.pretty_struct("Directive:Import")
                    .field("path", path)
                    .field("alias", alias)
                    .finish()?;

                ctx.print_loc(loc)?;

                Ok(())
            }
            Self::Mod { name, loc } => {
                ctx.pretty_struct("Directive:Mod")
                    .field("name", name)
                    .finish()?;

                ctx.print_loc(loc)?;

                Ok(())
            }
        }
    }
}

impl PrettyDump for DsExpression {
    fn try_dump(&self, ctx: &mut PrettyCtxt) -> io::Result<()> {
        self.expr.try_dump(ctx)?;
        ctx.print_loc(&self.loc)?;
        Ok(())
    }
}

impl PrettyDump for DsExprKind {
    fn try_dump(&self, ctx: &mut PrettyCtxt) -> io::Result<()> {
        let out = &mut ctx.out;

        match self {
            DsExprKind::Lit(lit) => write!(out, "{lit}"),
            DsExprKind::BoolLit(b) => write!(out, "boolean {b}"),
            DsExprKind::Ident(lazysym) => lazysym.try_dump(ctx),
            DsExprKind::Binary { lhs, op, rhs } => {
                ctx.pretty_struct("Binary")
                    .field("lhs", lhs)
                    .field("op", op)
                    .field("rhs", rhs)
                    .finish()?;

                Ok(())
            }
            DsExprKind::Unary { op, expr } => {
                ctx.pretty_struct("Unary")
                    .field("op", op)
                    .field("expr", expr)
                    .finish()?;

                Ok(())
            }
            DsExprKind::Borrow { mutable, expr } => {
                ctx.pretty_struct("Borrow")
                    .field("mutable", mutable)
                    .field("expr", expr)
                    .finish()?;

                Ok(())
            }
            DsExprKind::FunCall { callee, args } => {
                ctx.pretty_struct("FunCall")
                    .field("callee", callee)
                    .field("args", args.as_slice())
                    .finish()?;

                Ok(())
            }
            DsExprKind::If {
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
            DsExprKind::Block { label, block } => {
                ctx.pretty_struct("Block")
                    .field(
                        "label",
                        (
                            label.clone().map(|l| l.0),
                            &label.clone().map(|l| l.1).unwrap_or(Span::ZERO),
                        ),
                    )
                    .field("block", block)
                    .finish()?;

                Ok(())
            }
            DsExprKind::Loop { label, body } => {
                ctx.pretty_struct("Loop")
                    .field(
                        "label",
                        (
                            label.clone().map(|l| l.0),
                            &label.clone().map(|l| l.1).unwrap_or(Span::ZERO),
                        ),
                    )
                    .field("body", body)
                    .finish()?;

                Ok(())
            }
            DsExprKind::Return { expr } => {
                ctx.pretty_struct("Return").field("expr", expr).finish()?;
                Ok(())
            }
            DsExprKind::Break { label, expr } => {
                ctx.pretty_struct("Break")
                    .field("label", label)
                    .field("expr", expr)
                    .finish()?;
                Ok(())
            }
            DsExprKind::Continue { label } => {
                if label.is_some() {
                    ctx.pretty_struct("Continue").field("label", label).finish()
                } else {
                    write!(ctx.out, "Continue")
                }
            }
            DsExprKind::Null => {
                write!(ctx.out, "Null")
            }
            DsExprKind::Field { expr, member } => {
                ctx.pretty_struct("Field")
                    .field("expr", expr)
                    .field("member", member)
                    .finish()?;

                Ok(())
            }
            DsExprKind::QualifiedPath { path, sym } => {
                ctx.pretty_struct("QualifiedPath")
                    .field("path", path)
                    .field("sym", sym)
                    .finish()?;

                Ok(())
            }
            DsExprKind::Underscore => write!(ctx.out, "Underscore"),
            DsExprKind::FunDefinition {
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
            DsExprKind::FunDeclaration { args, rettypexpr } => {
                ctx.pretty_struct("FunDeclaration")
                    .field("args", args.as_slice())
                    .field("rettypexpr", rettypexpr)
                    .finish()?;

                Ok(())
            }
            DsExprKind::PointerType { mutable, typexpr } => {
                ctx.pretty_struct("PointerType")
                    .field("mutable", mutable)
                    .field("typexpr", typexpr)
                    .finish()?;

                Ok(())
            }
            DsExprKind::FunPtrType { args, ret } => {
                ctx.pretty_struct("FunPtrType")
                    .field("args", args.as_slice())
                    .field("ret", ret)
                    .finish()?;

                Ok(())
            }
            DsExprKind::Poisoned { diag } => {
                write!(ctx.out, "POISONED: {diag:#?}")
            }
        }
    }
}

impl PrettyDump for DsArg {
    fn try_dump(&self, ctx: &mut PrettyCtxt) -> io::Result<()> {
        let DsArg {
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

impl PrettyDump for DsBlock {
    fn try_dump(&self, ctx: &mut PrettyCtxt) -> io::Result<()> {
        struct LastExpr<'a>(&'a Option<Box<DsExpression>>);

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

impl PrettyDump for DsStatement {
    fn try_dump(&self, ctx: &mut PrettyCtxt) -> io::Result<()> {
        self.stmt.try_dump(ctx)?;
        ctx.print_loc(&self.loc)?;
        Ok(())
    }
}

impl PrettyDump for DsStmt {
    fn try_dump(&self, ctx: &mut PrettyCtxt) -> io::Result<()> {
        match self {
            DsStmt::VariableDef {
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
            DsStmt::Defer { expr } => {
                ctx.pretty_struct("Defer").field("expr", expr).finish()?;
                Ok(())
            }
            DsStmt::Expression(expr) => {
                expr.try_dump(ctx)?;
                Ok(())
            }
        }
    }
}
