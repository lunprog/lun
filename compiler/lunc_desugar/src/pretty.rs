//! Pretty printing for DSIR.

use std::io::{self, Write};

use lunc_entity::EntityDb;
use lunc_utils::{
    pretty::{PrettyCtxt, PrettyDump},
    pretty_struct,
};

use crate::{
    DsArg, DsBlock, DsDirective, DsExprKind, DsExpression, DsItem, DsModule, DsStatement,
    DsStmtKind, symbol::Symbol,
};

impl PrettyDump<EntityDb<Symbol>> for DsModule {
    fn try_dump(&self, ctx: &mut PrettyCtxt, extra: &EntityDb<Symbol>) -> io::Result<()> {
        self.items.as_slice().try_dump(ctx, extra)
    }
}

impl PrettyDump<EntityDb<Symbol>> for DsItem {
    fn try_dump(&self, ctx: &mut PrettyCtxt, extra: &EntityDb<Symbol>) -> io::Result<()> {
        match self {
            DsItem::GlobalDef {
                name,
                mutability,
                typeexpr,
                value,
                loc,
                sym,
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
                        sym,
                    },
                    loc
                );

                Ok(())
            }
            DsItem::GlobalUninit {
                name,
                typeexpr,
                loc,
                sym,
            } => {
                pretty_struct! (
                    ctx,
                    extra,
                    "GlobalUninit",
                    {
                        name,
                        typeexpr,
                        sym,
                    },
                    loc
                );

                Ok(())
            }
            DsItem::Module {
                name,
                module,
                loc,
                sym,
            } => {
                pretty_struct! (
                    ctx,
                    extra,
                    "Module",
                    {
                        name,
                        module,
                        sym,
                    },
                    loc
                );

                Ok(())
            }
            DsItem::ExternBlock { abi, items, loc } => {
                pretty_struct! (
                    ctx,
                    extra,
                    "ExternalBlock",
                    {
                        abi,
                        items,
                    },
                    loc
                );

                Ok(())
            }
            DsItem::Directive(directive) => directive.try_dump(ctx, extra),
        }
    }
}

impl PrettyDump<EntityDb<Symbol>> for DsDirective {
    fn try_dump(&self, ctx: &mut PrettyCtxt, extra: &EntityDb<Symbol>) -> io::Result<()> {
        match self {
            Self::Import { path, alias, loc } => {
                pretty_struct! (
                    ctx,
                    extra,
                    "Directive:Import",
                    {
                        path,
                        alias
                    },
                    loc
                );

                Ok(())
            }
            Self::Mod { name, loc } => {
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
        }
    }
}

impl PrettyDump<EntityDb<Symbol>> for DsExpression {
    fn try_dump(&self, ctx: &mut PrettyCtxt, extra: &EntityDb<Symbol>) -> io::Result<()> {
        self.expr.try_dump(ctx, extra)?;
        ctx.print_loc(&self.loc)?;
        Ok(())
    }
}

impl PrettyDump<EntityDb<Symbol>> for DsExprKind {
    fn try_dump(&self, ctx: &mut PrettyCtxt, extra: &EntityDb<Symbol>) -> io::Result<()> {
        let out = &mut ctx.out;

        match self {
            DsExprKind::Lit(lit) => write!(out, "{lit}"),
            DsExprKind::BoolLit(b) => write!(out, "boolean {b}"),
            DsExprKind::Path(lazysym) => lazysym.try_dump(ctx, extra),
            DsExprKind::Binary { lhs, op, rhs } => {
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
            DsExprKind::Unary { op, expr } => {
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
            DsExprKind::Borrow(mutability, expr) => {
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
            DsExprKind::Call { callee, args } => {
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
            DsExprKind::If {
                cond,
                then_br,
                else_br,
            } => {
                pretty_struct! (
                    ctx,
                    extra,
                    "If",
                    {
                        cond,
                        then_br,
                        else_br,
                    },
                );

                Ok(())
            }
            DsExprKind::Block { label, block } => {
                pretty_struct! (
                    ctx,
                    extra,
                    "Block",
                    {
                        label,
                        block,
                    },
                );

                Ok(())
            }
            DsExprKind::Loop { label, body } => {
                pretty_struct! (
                    ctx,
                    extra,
                    "Loop",
                    {
                        label,
                        body,
                    },
                );

                Ok(())
            }
            DsExprKind::Return { expr } => {
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
            DsExprKind::Break { label, expr } => {
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
            DsExprKind::Continue { label } => {
                if let Some(label) = label {
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
            DsExprKind::Null => {
                write!(ctx.out, "Null")
            }
            DsExprKind::Field {
                expr,
                field: member,
            } => {
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
            DsExprKind::Underscore => write!(ctx.out, "Underscore"),
            DsExprKind::FunDefinition {
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
            DsExprKind::FunDeclaration { args, rettypeexpr } => {
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
            DsExprKind::PointerType(mutability, typeexpr) => {
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
            DsExprKind::FunPtrType { args, ret } => {
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
            DsExprKind::Poisoned { diag } => {
                write!(ctx.out, "POISONED: {diag:#?}")
            }
        }
    }
}

impl PrettyDump<EntityDb<Symbol>> for DsArg {
    fn try_dump(&self, ctx: &mut PrettyCtxt, extra: &EntityDb<Symbol>) -> io::Result<()> {
        let DsArg {
            name,
            typeexpr,
            loc,
            sym,
        } = self;

        pretty_struct! (
            ctx,
            extra,
            "Arg",
            {
                name,
                typeexpr,
                sym,
            },
            loc
        );

        Ok(())
    }
}

impl PrettyDump<EntityDb<Symbol>> for DsBlock {
    fn try_dump(&self, ctx: &mut PrettyCtxt, extra: &EntityDb<Symbol>) -> io::Result<()> {
        struct LastExpr<'a>(&'a Option<Box<DsExpression>>);

        impl<'a> PrettyDump<EntityDb<Symbol>> for LastExpr<'a> {
            fn try_dump(&self, ctx: &mut PrettyCtxt, extra: &EntityDb<Symbol>) -> io::Result<()> {
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

impl PrettyDump<EntityDb<Symbol>> for DsStatement {
    fn try_dump(&self, ctx: &mut PrettyCtxt, extra: &EntityDb<Symbol>) -> io::Result<()> {
        self.stmt.try_dump(ctx, extra)?;
        ctx.print_loc(&self.loc)?;
        Ok(())
    }
}

impl PrettyDump<EntityDb<Symbol>> for DsStmtKind {
    fn try_dump(&self, ctx: &mut PrettyCtxt, extra: &EntityDb<Symbol>) -> io::Result<()> {
        match self {
            DsStmtKind::BindingDef {
                name,
                mutability,
                typeexpr,
                value,
                sym,
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
                        sym,
                    },
                );

                Ok(())
            }
            DsStmtKind::Defer { expr } => {
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
            DsStmtKind::Expression(expr) => {
                expr.try_dump(ctx, extra)?;

                Ok(())
            }
        }
    }
}
