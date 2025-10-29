//! Pretty tree printer, used for printing the AST, the DSIR, and the HTIR

use std::io::{self, Write};

use crate::Span;

#[macro_export]
macro_rules! pretty_struct {
    ($ctx:expr, $extra:expr, $name:tt, { $( $field:ident ),* $(,)? } $(,)? $( , $loc:expr )?) => {
        $crate::pretty::is_pretty_ctxt($ctx);

        let name = $name;

        if name.is_empty() {
            writeln!($ctx.out, "{{")?;
        } else {
            writeln!($ctx.out, "{name} {{")?;
        }

        $ctx.indent();

        $(
            $ctx.write_indent()?;

            write!($ctx.out, "{}: ", std::stringify!($field))?;
            PrettyDump::try_dump($field, $ctx, $extra)?;
            writeln!($ctx.out, ";")?;
        )*

        $ctx.dedent();
        $ctx.write_indent()?;
        write!($ctx.out, "}}")?;

        $(
            $ctx.print_loc($loc)?;
        )?
    };
}

#[doc(hidden)]
pub fn is_pretty_ctxt(_: &mut PrettyCtxt) {}

/// Helper trait to allow passing `(name, name_loc)` instead of `&(name, name_loc)`
pub trait AsPrettyDump<E> {
    fn as_pretty_dump(&self) -> &dyn PrettyDump<E>;
}

impl<T: PrettyDump<E>, E> AsPrettyDump<E> for T {
    fn as_pretty_dump(&self) -> &dyn PrettyDump<E> {
        self
    }
}

/// A list helping struct to dump list-like tree nodes
pub struct ListDump<'ctx, 'w, E> {
    ctx: &'ctx mut PrettyCtxt<'w>,
    res: io::Result<()>,
    finished: bool,
    is_empty: bool,
    extra: E,
}

impl<'ctx, 'w, E> ListDump<'ctx, 'w, E> {
    pub fn item(mut self, item: impl AsPrettyDump<E>) -> ListDump<'ctx, 'w, E> {
        let item = item.as_pretty_dump();
        if self.finished {
            self.res = Err(io::Error::other("StructDump already finished"));
            return self;
        }
        if self.res.is_ok() {
            self.res = (|| {
                writeln!(self.ctx.out)?;
                self.ctx.write_indent()?;
                item.try_dump(self.ctx, &self.extra)?;
                writeln!(self.ctx.out, ",")?;
                self.is_empty = false;

                Ok(())
            })();
        }

        self
    }

    pub fn items<I: AsPrettyDump<E>>(
        mut self,
        items: impl Iterator<Item = I>,
    ) -> ListDump<'ctx, 'w, E> {
        if self.finished {
            self.res = Err(io::Error::other("ListDump already finished"));
            return self;
        }

        if self.res.is_ok() {
            self.res = (|| {
                for item in items {
                    let item = item.as_pretty_dump();

                    writeln!(self.ctx.out)?;
                    self.ctx.write_indent()?;
                    item.try_dump(self.ctx, &self.extra)?;
                    writeln!(self.ctx.out, ",")?;
                    self.is_empty = false;
                }

                Ok(())
            })();
        }

        self
    }

    pub fn finish(mut self) -> io::Result<()> {
        if self.finished {
            return self.res;
        }

        if self.res.is_ok() {
            self.res = (|| {
                self.ctx.dedent();

                if !self.is_empty {
                    self.ctx.write_indent()?;
                }
                write!(self.ctx.out, "]")
            })();
        }

        self.finished = true;
        self.res
    }
}

/// Wrapper around either an owned or borrowed writer.
pub enum Writer<'w> {
    Owned(Box<dyn Write>),
    Borrowed(&'w mut dyn Write),
}

impl<'w> Writer<'w> {
    pub fn owned(writer: impl Write + 'static) -> Writer<'w> {
        Writer::Owned(Box::new(writer))
    }
}

impl<'w> Write for Writer<'w> {
    fn write(&mut self, buf: &[u8]) -> io::Result<usize> {
        match self {
            Writer::Owned(w) => w.write(buf),
            Writer::Borrowed(w) => w.write(buf),
        }
    }

    fn flush(&mut self) -> io::Result<()> {
        match self {
            Writer::Owned(w) => w.flush(),
            Writer::Borrowed(w) => w.flush(),
        }
    }
}

impl<'w> From<&'w mut dyn Write> for Writer<'w> {
    fn from(value: &'w mut dyn Write) -> Self {
        Writer::Borrowed(value)
    }
}

/// Context of pretty printing trees
pub struct PrettyCtxt<'w> {
    /// indent amount (count of spaces)
    indent: usize,
    /// current indentation amount, (count of spaces)
    current_indent: usize,
    pub out: Writer<'w>,
}

impl<'w> PrettyCtxt<'w> {
    pub const DEFAULT_INDENT: usize = 2;

    /// create a new pretty context
    pub fn new(indent: usize, out: impl Into<Writer<'w>>) -> PrettyCtxt<'w> {
        PrettyCtxt {
            indent,
            current_indent: 0,
            out: out.into(),
        }
    }

    /// write the current indentation
    pub fn write_indent(&mut self) -> io::Result<()> {
        write!(self.out, "{:1$}", "", self.current_indent)
    }

    /// increase the indent level by one indent
    pub fn indent(&mut self) {
        self.current_indent += self.indent;
    }

    /// decrease the indent level by one indent
    pub fn dedent(&mut self) {
        self.current_indent -= self.indent;
    }

    /// create a new helper for list-like tree nodes dump
    pub fn pretty_list<'ctx, E: Clone>(
        &'ctx mut self,
        name: Option<String>,
        extra: &E,
    ) -> ListDump<'ctx, 'w, E> {
        let res = (|| {
            if let Some(name) = name {
                write!(self.out, "{name} ")?;
            }
            write!(self.out, "[")?;
            self.indent();
            Ok(())
        })();

        ListDump {
            ctx: self,
            res,
            finished: false,
            is_empty: true,
            extra: extra.clone(),
        }
    }

    /// Print the location attached to a node
    pub fn print_loc<'a>(&mut self, loc: impl Into<Option<&'a Span>>) -> io::Result<()> {
        if let Some(loc) = loc.into() {
            write!(self.out, " @ {loc}")
        } else {
            write!(self.out, " @ none")
        }
    }
}

impl<'w> Default for PrettyCtxt<'w> {
    fn default() -> Self {
        PrettyCtxt::new(PrettyCtxt::DEFAULT_INDENT, Writer::owned(io::stderr()))
    }
}

/// Dump a tree, but the Pretty version.
///
/// # `E` generic
///
/// It is here if you need extra context to pretty dump.
pub trait PrettyDump<E> {
    fn try_dump(&self, ctx: &mut PrettyCtxt, extra: &E) -> io::Result<()>;

    /// Dump the current node with the defaults of PrettyCtxt, to stderr.
    #[inline]
    #[track_caller]
    fn dump(&self, extra: &E) {
        self.try_dump(&mut PrettyCtxt::default(), extra).unwrap()
    }

    /// Dumps the node with the default indent level to the writer `out`.
    #[inline]
    #[track_caller]
    fn dump_to(&self, out: &mut dyn Write, extra: &E) {
        let mut ctx = PrettyCtxt::new(PrettyCtxt::DEFAULT_INDENT, out);
        self.try_dump(&mut ctx, extra).unwrap()
    }
}

impl<T: PrettyDump<E>, const N: usize, E: Clone> PrettyDump<E> for [T; N] {
    fn try_dump(&self, ctx: &mut PrettyCtxt, e: &E) -> io::Result<()> {
        (&self[..]).try_dump(ctx, e)
    }
}

impl<T: PrettyDump<E>, E: Clone> PrettyDump<E> for &[T] {
    fn try_dump(&self, ctx: &mut PrettyCtxt, extra: &E) -> io::Result<()> {
        ctx.pretty_list(None, extra).items(self.iter()).finish()?;

        Ok(())
    }
}

impl<'ctx, 'w, E> PrettyDump<E> for ListDump<'ctx, 'w, E> {
    fn try_dump(&self, _: &mut PrettyCtxt, _: &E) -> io::Result<()> {
        assert!(self.finished);
        // we already printed everything
        Ok(())
    }
}

impl<E> PrettyDump<E> for String {
    fn try_dump(&self, ctx: &mut PrettyCtxt, extra: &E) -> io::Result<()> {
        self.as_str().try_dump(ctx, extra)
    }
}

impl<T: PrettyDump<E>, E> PrettyDump<E> for &T {
    fn try_dump(&self, ctx: &mut PrettyCtxt, extra: &E) -> io::Result<()> {
        T::try_dump(self, ctx, extra)
    }
}

impl<T: PrettyDump<E>, E> PrettyDump<E> for &mut T {
    fn try_dump(&self, ctx: &mut PrettyCtxt, extra: &E) -> io::Result<()> {
        T::try_dump(self, ctx, extra)
    }
}

impl<T: PrettyDump<E>, E> PrettyDump<E> for Option<T> {
    fn try_dump(&self, ctx: &mut PrettyCtxt, extra: &E) -> io::Result<()> {
        if let Some(node) = self {
            node.try_dump(ctx, extra)
        } else {
            write!(ctx.out, "none")
        }
    }
}

impl<T: PrettyDump<E>, E> PrettyDump<E> for (T, &Option<Span>) {
    fn try_dump(&self, ctx: &mut PrettyCtxt, extra: &E) -> io::Result<()> {
        self.0.try_dump(ctx, extra)?;
        ctx.print_loc(self.1)?;
        Ok(())
    }
}

impl<T: PrettyDump<E>, E> PrettyDump<E> for Box<T> {
    fn try_dump(&self, ctx: &mut PrettyCtxt, extra: &E) -> io::Result<()> {
        T::try_dump(self, ctx, extra)
    }
}

impl<T: PrettyDump<E>, E: Clone> PrettyDump<E> for Vec<T> {
    fn try_dump(&self, ctx: &mut PrettyCtxt, extra: &E) -> io::Result<()> {
        <&[T]>::try_dump(&self.as_slice(), ctx, extra)
    }
}

/// A macro to implement pretty dump for a type that implements display
#[macro_export]
macro_rules! impl_pdump {
    ($T:ty) => {
        impl<E> $crate::pretty::PrettyDump<E> for $T {
            fn try_dump(&self, ctx: &mut $crate::pretty::PrettyCtxt, _: &E) -> ::std::io::Result<()> {
                use ::std::io::Write;
                write!(ctx.out, "{self}")
            }
        }
    };
    ( $T:ty $(, $U:ty )* $( , )? ) => {
        impl_pdump!($T);
        $(
            impl_pdump!($U);
        )*
    }
}

impl_pdump! {
    Span,
    bool,
    char,
    &str,
    u8,
    u16,
    u32,
    u64,
    u128,
    usize,
    i8,
    i16,
    i32,
    i64,
    i128,
    isize,
    // f16,
    f32,
    f64,
    // f128,
}
