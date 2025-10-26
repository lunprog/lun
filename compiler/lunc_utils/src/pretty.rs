//! Pretty tree printer, used for printing the AST, the DSIR, and the HTIR

use std::io::{self, Write};

use crate::Span;

/// A struct helping to dump tree where you encounter a struct
pub struct StructDump<'ctx, 'w> {
    ctx: &'ctx mut PrettyCtxt<'w>,
    res: io::Result<()>,
    finished: bool,
}

impl<'ctx, 'w> StructDump<'ctx, 'w> {
    pub fn field(mut self, name: &str, field: impl AsPrettyDump) -> Self {
        let field = field.as_pretty_dump();

        if self.finished {
            self.res = Err(io::Error::other("StructDump already finished"));
            return self;
        }

        if self.res.is_ok() {
            self.res = (|| {
                self.ctx.write_indent()?;

                write!(self.ctx.out, "{name}: ")?;
                field.try_dump(self.ctx)?;
                writeln!(self.ctx.out, ";")
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
                self.ctx.deindent();

                self.ctx.write_indent()?;
                write!(self.ctx.out, "}}")
            })();
        }

        self.finished = true;
        self.res
    }
}

/// Helper trait to allow passing `(name, name_loc)` instead of `&(name, name_loc)`
pub trait AsPrettyDump {
    fn as_pretty_dump(&self) -> &dyn PrettyDump;
}

impl<T: PrettyDump> AsPrettyDump for T {
    fn as_pretty_dump(&self) -> &dyn PrettyDump {
        self
    }
}

/// A list helping struct to dump list-like tree nodes
pub struct ListDump<'ctx, 'w> {
    ctx: &'ctx mut PrettyCtxt<'w>,
    res: io::Result<()>,
    finished: bool,
    is_empty: bool,
}

impl<'ctx, 'w> ListDump<'ctx, 'w> {
    pub fn item(mut self, item: impl AsPrettyDump) -> ListDump<'ctx, 'w> {
        let item = item.as_pretty_dump();
        if self.finished {
            self.res = Err(io::Error::other("StructDump already finished"));
            return self;
        }
        if self.res.is_ok() {
            self.res = (|| {
                writeln!(self.ctx.out)?;
                self.ctx.write_indent()?;
                item.try_dump(self.ctx)?;
                writeln!(self.ctx.out, ",")?;
                self.is_empty = false;

                Ok(())
            })();
        }

        self
    }

    pub fn items<I: AsPrettyDump>(mut self, items: impl Iterator<Item = I>) -> ListDump<'ctx, 'w> {
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
                    item.try_dump(self.ctx)?;
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
                self.ctx.deindent();

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
    pub fn deindent(&mut self) {
        self.current_indent -= self.indent;
    }

    /// create a new dump of a struct, used to assist tree dumping when there
    /// is a struct
    pub fn pretty_struct<'ctx>(&'ctx mut self, name: &str) -> StructDump<'ctx, 'w> {
        let res = (|| {
            if name.is_empty() {
                writeln!(self.out, "{{")?;
            } else {
                writeln!(self.out, "{name} {{")?;
            }
            self.indent();

            Ok(())
        })();

        StructDump {
            ctx: self,
            res,
            finished: false,
        }
    }

    /// create a new helper for list-like tree nodes dump
    pub fn pretty_list<'ctx>(&'ctx mut self, name: Option<String>) -> ListDump<'ctx, 'w> {
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
pub trait PrettyDump {
    fn try_dump(&self, ctx: &mut PrettyCtxt) -> io::Result<()>;

    /// Dump the current node with the defaults of PrettyCtxt, to stderr.
    #[inline]
    #[track_caller]
    fn dump(&self) {
        self.try_dump(&mut PrettyCtxt::default()).unwrap()
    }

    /// Dumps the node with the default indent level to the writer `out`.
    #[inline]
    #[track_caller]
    fn dump_to(&self, out: &mut dyn Write) {
        let mut ctx = PrettyCtxt::new(PrettyCtxt::DEFAULT_INDENT, out);
        self.try_dump(&mut ctx).unwrap()
    }
}

impl<T: PrettyDump, const N: usize> PrettyDump for [T; N] {
    fn try_dump(&self, ctx: &mut PrettyCtxt) -> io::Result<()> {
        (&self[..]).try_dump(ctx)
    }
}

impl<T: PrettyDump> PrettyDump for &[T] {
    fn try_dump(&self, ctx: &mut PrettyCtxt) -> io::Result<()> {
        ctx.pretty_list(None).items(self.iter()).finish()?;

        Ok(())
    }
}

impl<'ctx, 'w> PrettyDump for StructDump<'ctx, 'w> {
    fn try_dump(&self, _: &mut PrettyCtxt) -> io::Result<()> {
        assert!(self.finished);
        // we already printed everything
        Ok(())
    }
}

impl<'ctx, 'w> PrettyDump for ListDump<'ctx, 'w> {
    fn try_dump(&self, _: &mut PrettyCtxt) -> io::Result<()> {
        assert!(self.finished);
        // we already printed everything
        Ok(())
    }
}

impl PrettyDump for String {
    fn try_dump(&self, ctx: &mut PrettyCtxt) -> io::Result<()> {
        self.as_str().try_dump(ctx)
    }
}

impl<T: PrettyDump> PrettyDump for &T {
    fn try_dump(&self, ctx: &mut PrettyCtxt) -> io::Result<()> {
        T::try_dump(self, ctx)
    }
}

impl<T: PrettyDump> PrettyDump for &mut T {
    fn try_dump(&self, ctx: &mut PrettyCtxt) -> io::Result<()> {
        T::try_dump(self, ctx)
    }
}

impl<T: PrettyDump> PrettyDump for Option<T> {
    fn try_dump(&self, ctx: &mut PrettyCtxt) -> io::Result<()> {
        if let Some(node) = self {
            node.try_dump(ctx)
        } else {
            write!(ctx.out, "none")
        }
    }
}

impl<T: PrettyDump> PrettyDump for (T, &Span) {
    fn try_dump(&self, ctx: &mut PrettyCtxt) -> io::Result<()> {
        self.0.try_dump(ctx)?;
        ctx.print_loc(self.1)?;
        Ok(())
    }
}

impl<T: PrettyDump> PrettyDump for (T, &Option<Span>) {
    fn try_dump(&self, ctx: &mut PrettyCtxt) -> io::Result<()> {
        self.0.try_dump(ctx)?;
        ctx.print_loc(self.1)?;
        Ok(())
    }
}

impl<T: PrettyDump> PrettyDump for Box<T> {
    fn try_dump(&self, ctx: &mut PrettyCtxt) -> io::Result<()> {
        T::try_dump(self, ctx)
    }
}

/// A macro to implement pretty dump for a type that implements display
#[macro_export]
macro_rules! impl_pdump {
    ($T:ty) => {
        impl $crate::pretty::PrettyDump for $T {
            fn try_dump(&self, ctx: &mut $crate::pretty::PrettyCtxt) -> ::std::io::Result<()> {
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
