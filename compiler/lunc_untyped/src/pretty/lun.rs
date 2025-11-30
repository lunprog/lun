//! Pretty-printing for [UTIR](crate::utir) in lun-like flavor.

use std::{
    io::{self, Write},
    rc::Rc,
    sync::Mutex,
};

use lunc_entity::Opt;
use lunc_utils::pretty::{PrettyCtxt, PrettyDump, pretty_to_string};

use crate::{pretty::LunFlavor, utir::*};

pub fn expr_to_string(expr: ExprId, item: ItemId, orb: &Orb) -> String {
    let dumper = OrbDumper(Rc::new(Mutex::new(OrbDumperInner {
        orb: &raw const *orb,
        item: Opt::None,
    })));

    dumper.set_item(item);

    pretty_to_string(dumper.body().exprs.get(expr), &dumper)
}

/// Struct used to [`PrettyDump`] SIR with the Lun-like Flavor.
///
/// # Note
///
/// It can only be created by `PrettyDump<LunFlavor>` implementation of `Orb`.
#[derive(Debug, Clone)]
pub struct OrbDumper(Rc<Mutex<OrbDumperInner>>);

impl OrbDumper {
    fn set_item(&self, item: ItemId) {
        let mut inner = self.0.lock().unwrap();

        inner.item = Opt::Some(item);
    }

    /// Get access to an item.
    #[allow(unused)]
    fn access<R>(&self, id: ItemId, mut accessor: impl FnMut(&Item) -> R) -> R {
        let inner = self.0.lock().unwrap();

        // SAFETY: lifetime of `orb` guaranteed by the creator of OrbDumpInner.
        unsafe { accessor((*inner.orb).items.get(id)) }
    }

    #[track_caller]
    fn access_c<'a, R: 'a>(&'a self, mut accessor: impl FnMut(&'a Item) -> R) -> R {
        let inner = self.0.lock().unwrap();

        // SAFETY: lifetime of `orb` guaranteed by the creator of OrbDumpInner.
        unsafe { accessor((*inner.orb).items.get(inner.item.unwrap())) }
    }

    #[track_caller]
    fn body(&self) -> &Body {
        self.access_c(|item| item.body())
    }

    fn dump_e(&self, ctx: &mut PrettyCtxt, id: ExprId) -> io::Result<()> {
        let expr = self.body().exprs.get(id);

        expr.try_dump(ctx, self)
    }

    fn param_name(&self, param: ParamId) -> &str {
        let Item::Fundef(Fundef { params, .. }) = self.access_c(|i| i) else {
            unreachable!()
        };

        &params.get(param).name.node
    }

    fn binding_name(&self, bind: BindingId) -> &str {
        &self.body().bindings.get(bind).name.node
    }
}

#[derive(Debug, Clone)]
struct OrbDumperInner {
    // NOTE: we use a raw pointer because we cannot have lifetimes here.
    // SAFETY: orb must live for the entirety of its use and not have any
    // mutable pointer/reference.
    orb: *const Orb,
    item: Opt<ItemId>,
}

impl PrettyDump<LunFlavor> for Orb {
    fn try_dump(&self, ctx: &mut PrettyCtxt, _: &LunFlavor) -> io::Result<()> {
        let Orb { items } = self;

        let dumper = OrbDumper(Rc::new(Mutex::new(OrbDumperInner {
            orb: &raw const *self,
            item: Opt::None,
        })));

        let mut first = true;

        for (id, item) in items.full_iter() {
            if first {
                first = false;
            } else {
                writeln!(ctx.out)?;
            }

            dumper.set_item(id);

            item.try_dump(ctx, &dumper)?;
        }

        Ok(())
    }
}

impl PrettyDump<OrbDumper> for Item {
    fn try_dump(&self, ctx: &mut PrettyCtxt, extra: &OrbDumper) -> io::Result<()> {
        match self {
            Item::Fundef(fundef) => fundef.try_dump(ctx, extra),
            _ => todo!(),
        }
    }
}

impl PrettyDump<OrbDumper> for Fundef {
    fn try_dump(&self, ctx: &mut PrettyCtxt, extra: &OrbDumper) -> io::Result<()> {
        let Fundef {
            name: _, // we print the path it's faster.
            path,
            typ: _, // we don't care printing the type for a fundef...
            params,
            ret_ty,
            entry,
            body,
            loc,
        } = self;

        write!(ctx.out, "{} :: fun(", path)?;

        let mut first = true;

        for Param { name, typ, loc: _ } in params.data_iter() {
            if first {
                first = false;
            } else {
                write!(ctx.out, ", ")?;
            }

            write!(ctx.out, "{}: ", name.node)?;
            typ.try_dump(ctx, extra)?;
        }

        _ = ret_ty;
        _ = entry;
        _ = body;
        _ = loc;

        Ok(())
    }
}

impl PrettyDump<OrbDumper> for Uty {
    fn try_dump(&self, ctx: &mut PrettyCtxt, extra: &OrbDumper) -> io::Result<()> {
        match *self {
            Uty::TyVar(_) => write!(ctx.out, "{{type-variable}}"),
            Uty::Expr(e) => extra.dump_e(ctx, e),
        }
    }
}

impl PrettyDump<OrbDumper> for Expr {
    fn try_dump(&self, ctx: &mut PrettyCtxt, extra: &OrbDumper) -> io::Result<()> {
        match self {
            Expr::Int(i) => write!(ctx.out, "{i}"),
            Expr::Char(c) => write!(ctx.out, "{c:?}"),
            Expr::Float(ieee) => write!(ctx.out, "{ieee}"),
            Expr::Str(str) => write!(ctx.out, "{str:?}"),
            Expr::CStr(cstr) => write!(ctx.out, "cstr{cstr:?}"),
            Expr::Bool(b) => write!(ctx.out, "{b}"),
            Expr::Item(item) => {
                _ = item;

                todo!("ADD PATH TO ITEMS")
            }
            Expr::Param(param) => {
                write!(ctx.out, "{}", extra.param_name(*param))
            }
            Expr::Binding(bind) => {
                write!(ctx.out, "{}", extra.binding_name(*bind))
            }
            Expr::Binary(lhs, binop, rhs) => {
                extra.dump_e(ctx, *lhs)?;
                write!(ctx.out, " {binop} ")?;
                extra.dump_e(ctx, *rhs)?;

                Ok(())
            }
            Expr::Unary(unop, expr) => {
                if unop.is_left() {
                    write!(ctx.out, "{unop}")?;
                }

                extra.dump_e(ctx, *expr)?;

                if unop.is_right() {
                    write!(ctx.out, "{unop}")?;
                }

                Ok(())
            }
            Expr::Borrow(mutab, expr) => {
                write!(ctx.out, "&{}", mutab.prefix_str())?;

                extra.dump_e(ctx, *expr)
            }
            Expr::Call { callee, args } => {
                extra.dump_e(ctx, *callee)?;
                write!(ctx.out, "(")?;

                let mut first = true;

                for arg in args {
                    if first {
                        first = false;
                    } else {
                        write!(ctx.out, ", ")?;
                    }

                    extra.dump_e(ctx, *arg)?;
                }

                write!(ctx.out, ")")?;

                Ok(())
            }
            Expr::PtrType(mutab, expr) => {
                write!(ctx.out, "*{}", mutab.prefix_str())?;

                extra.dump_e(ctx, *expr)
            }
            Expr::FunptrType(params, ret) => {
                write!(ctx.out, "*fun(")?;

                let mut first = true;

                for param in params {
                    if first {
                        first = false;
                    } else {
                        write!(ctx.out, ", ")?;
                    }

                    extra.dump_e(ctx, *param)?;
                }
                write!(ctx.out, ")")?;

                if let Some(ret) = ret.expand() {
                    write!(ctx.out, "-> ")?;
                    extra.dump_e(ctx, ret)?;
                }

                Ok(())
            }
            Expr::PrimType(ptype) => {
                write!(ctx.out, "{ptype}")
            }
            e => todo!("{e:?}"),
        }
    }
}
