//! Pretty printing for DSIR.

use std::io;

use lunc_utils::pretty::{PrettyCtxt, PrettyDump};

use crate::{
    DsArg, DsBlock, DsExpr, DsExpression, DsItem, DsItemDirective, DsModule, DsStatement, DsStmt,
    LazySymbol, Symbol,
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
                typ,
                value,
                loc,
            } => {
                ctx.pretty_struct("GlobalDef")
                    .field("name", (name, name_loc))
                    .field("mutable", mutable)
                    .field("typ", typ)
                    .field("value", value)
                    .finish()?;

                ctx.print_loc(loc)?;
                Ok(())
            }
            DsItem::Module { name, module, loc } => {
                ctx.pretty_struct("Module")
                    .field("name", (name, loc))
                    .field("module", module)
                    .finish()?;

                Ok(())
            }
            DsItem::Directive(directive) => directive.try_dump(ctx),
        }
    }
}

impl PrettyDump for DsItemDirective {
    fn try_dump(&self, ctx: &mut PrettyCtxt) -> io::Result<()> {
        match self {
            Self::Use { path, alias, loc } => {
                ctx.pretty_struct("Directive:Use")
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

impl PrettyDump for DsExpr {
    fn try_dump(&self, ctx: &mut PrettyCtxt) -> io::Result<()> {
        let out = &mut ctx.out;

        match self {
            DsExpr::IntLit(i) => write!(out, "integer {i}"),
            DsExpr::BoolLit(b) => write!(out, "boolean {b}"),
            DsExpr::StringLit(s) => write!(out, "string {s:?}"),
            DsExpr::CharLit(c) => write!(out, "character {c:?}"),
            DsExpr::FloatLit(f) => write!(out, "float {f:.}"),
            DsExpr::Ident(lazysym) => lazysym.try_dump(ctx),
            DsExpr::Binary { lhs, op, rhs } => {
                ctx.pretty_struct("Binary")
                    .field("lhs", lhs)
                    .field("op", op)
                    .field("rhs", rhs)
                    .finish()?;

                Ok(())
            }
            DsExpr::Unary { op, expr } => {
                ctx.pretty_struct("Unary")
                    .field("op", op)
                    .field("expr", expr)
                    .finish()?;

                Ok(())
            }
            DsExpr::AddressOf { mutable, val } => {
                ctx.pretty_struct("AddressOf")
                    .field("mutable", mutable)
                    .field("expr", val)
                    .finish()?;

                Ok(())
            }
            DsExpr::FunCall { callee, args } => {
                ctx.pretty_struct("FunCall")
                    .field("callee", callee)
                    .field("args", args.as_slice())
                    .finish()?;

                Ok(())
            }
            DsExpr::If {
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
            DsExpr::Block(block) => {
                write!(ctx.out, "Block ")?;
                block.try_dump(ctx)?;
                Ok(())
            }
            DsExpr::Loop { body } => {
                ctx.pretty_struct("Loop").field("body", body).finish()?;

                Ok(())
            }
            DsExpr::Return { val } => {
                ctx.pretty_struct("Return").field("val", val).finish()?;
                Ok(())
            }
            DsExpr::Break { val } => {
                ctx.pretty_struct("Break").field("val", val).finish()?;
                Ok(())
            }
            DsExpr::Continue => {
                write!(ctx.out, "Continue")
            }
            DsExpr::Null => {
                write!(ctx.out, "Null")
            }
            DsExpr::MemberAccess { expr, member } => {
                ctx.pretty_struct("MemberAccess")
                    .field("expr", expr)
                    .field("member", member)
                    .finish()?;

                Ok(())
            }
            DsExpr::Orb => {
                write!(ctx.out, "Orb")
            }
            DsExpr::FunDefinition {
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
            DsExpr::PointerType { mutable, typ } => {
                ctx.pretty_struct("PointerType")
                    .field("mutable", mutable)
                    .field("typ", typ)
                    .finish()?;

                Ok(())
            }
            DsExpr::FunPtrType { args, ret } => {
                ctx.pretty_struct("FunPtrType")
                    .field("args", args.as_slice())
                    .field("ret", ret)
                    .finish()?;

                Ok(())
            }
        }
    }
}

impl PrettyDump for LazySymbol {
    fn try_dump(&self, ctx: &mut PrettyCtxt) -> io::Result<()> {
        match self {
            LazySymbol::Name(id) => write!(ctx.out, "lazy {id}"),
            LazySymbol::Sym(sym) => sym.try_dump(ctx),
        }
    }
}

impl PrettyDump for Symbol {
    fn try_dump(&self, ctx: &mut PrettyCtxt) -> io::Result<()> {
        let Symbol { name, loc } = self;

        ctx.pretty_struct("Symbol")
            .field("name", (name, loc))
            .finish()?;

        Ok(())
    }
}

impl PrettyDump for DsArg {
    fn try_dump(&self, ctx: &mut PrettyCtxt) -> io::Result<()> {
        let DsArg {
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

        ctx.pretty_list()
            .items(self.stmts.iter())
            .items(last.0.iter())
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
