//! DSIR symbol

use std::{
    fmt::{self, Display},
    io,
};

use lunc_ast::{Mutability, Path, PathSegment};
use lunc_entity::{EntityDb, entity};
use lunc_utils::{
    Span, impl_pdump,
    pretty::{PrettyCtxt, PrettyDump},
};

/// Symbol entity, see also [`SymbolData`].
///
/// This is used in the DSIR stage to bring idents more informations on what do
/// they refer to.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Symbol(u32);

entity!(Symbol, SymbolData);

pub(crate) trait EntityDbExt {
    fn create_user_binding(
        &mut self,
        mutability: Mutability,
        name: String,
        ordinal: usize,
        loc: Span,
    ) -> Symbol;

    fn create_param(&mut self, name: String, ordinal: usize, loc: Span) -> Symbol;

    fn create_global_def(
        &mut self,
        mutability: Mutability,
        name: String,
        path: Path,
        loc: Span,
    ) -> Symbol;

    fn create_function(&mut self, name: String, path: Path, loc: Span) -> Symbol;

    fn create_module(&mut self, name: String, path: Path, loc: Span) -> Symbol;

    fn create_primitive_type(&mut self, name: &'static str) -> Symbol;
}

impl EntityDbExt for EntityDb<Symbol> {
    fn create_user_binding(
        &mut self,
        mutability: Mutability,
        name: String,
        ordinal: usize,
        loc: Span,
    ) -> Symbol {
        self.create(SymbolData {
            kind: SymbolKind::UserBinding(mutability),
            path: Path::with_root(PathSegment::Ident(name.clone())),
            name,
            ordinal,
            loc,
        })
    }

    fn create_param(&mut self, name: String, ordinal: usize, loc: Span) -> Symbol {
        self.create(SymbolData {
            kind: SymbolKind::Param,
            path: Path::with_root(PathSegment::Ident(name.clone())),
            name,
            ordinal,
            loc,
        })
    }

    fn create_global_def(
        &mut self,
        mutability: Mutability,
        name: String,
        path: Path,
        loc: Span,
    ) -> Symbol {
        self.create(SymbolData {
            kind: SymbolKind::GlobalDef(mutability),
            name,
            ordinal: 0,
            path,
            loc,
        })
    }

    fn create_function(&mut self, name: String, path: Path, loc: Span) -> Symbol {
        self.create(SymbolData {
            kind: SymbolKind::Function,
            name,
            ordinal: 0,
            path,
            loc,
        })
    }

    fn create_module(&mut self, name: String, path: Path, loc: Span) -> Symbol {
        self.create(SymbolData {
            kind: SymbolKind::Module,
            name,
            ordinal: 0,
            path,
            loc,
        })
    }

    fn create_primitive_type(&mut self, name: &'static str) -> Symbol {
        self.create(SymbolData {
            kind: SymbolKind::PrimitiveType,
            name: name.to_string(),
            ordinal: 0,
            path: Path::new(),
            loc: Span::ZERO,
        })
    }
}

/// The actual data stored in a [`Symbol`].
#[derive(Debug, Clone)]
pub struct SymbolData {
    /// Kind of Symbol
    pub kind: SymbolKind,
    /// Name of the symbol
    pub name: String,
    /// The ordinal of a symbol in the DSIR.
    ///
    /// eg:
    /// - for a function the `which` of the first argument is 0, the second is 1
    /// - for a variable the `which` is set to 0 for the first variable, 1 for the
    ///   second etc..
    /// - for a global and a function this field is not really relevant, but is
    ///   still populated
    pub ordinal: usize,
    /// the absolute path to the symbol
    pub path: Path,
    /// location of the identifier defining this symbol
    pub loc: Span,
}

/// Kind of [`Symbol`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SymbolKind {
    /// Function parameter
    Param,
    /// User binding
    UserBinding(Mutability),
    /// Global def
    GlobalDef(Mutability),
    /// Function definition or declaration
    Function,
    /// Module
    ///
    /// # Note
    ///
    /// Unlike other [`SymbolKind`]s this one is not a first-class citizen, you
    /// can't have an expression containing a symbol with `Module` kind.
    Module,
    /// Primitive type
    ///
    /// # Note
    ///
    /// This one is a special one, symbols with this kind can have very limited
    /// names and are reserved for the primitive types (as the name suggests..).
    PrimitiveType,
}

impl SymbolKind {
    pub fn is_global_def(&self) -> bool {
        matches!(self, Self::GlobalDef { .. } | Self::Function | Self::Module)
    }

    /// Can this kind of symbol allow shadowing?
    pub fn can_shadow(&self, other: &Self) -> bool {
        if *self == SymbolKind::Param && *other == SymbolKind::Param {
            return false;
        }

        matches!(
            (self, other),
            (
                Self::UserBinding { .. } | Self::Param,
                Self::UserBinding { .. }
                    | Self::Param
                    | Self::GlobalDef { .. }
                    | Self::Function
                    | Self::Module,
            )
        )
    }
}

impl Display for SymbolKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Param => write!(f, "parameter"),
            Self::UserBinding(mutability) => write!(f, "user-binding {}", mutability.suffix_str()),
            Self::GlobalDef(mutability) => write!(f, "global-def {}", mutability.suffix_str()),
            Self::Function => write!(f, "function"),
            Self::Module => write!(f, "module"),
            Self::PrimitiveType => write!(f, "primitive type"),
        }
    }
}

impl_pdump!(SymbolKind);

/// A maybe not yet evaluated Symbol
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum LazySymbol {
    Path(Path),
    Sym(Symbol),
}

impl LazySymbol {
    /// Unwraps the lazy symbol to a symbol
    ///
    /// # Panic
    ///
    /// This functions panics if it is called on a [`LazySymbol::Name(..)`]
    /// variant.
    pub fn unwrap_sym(&self) -> Symbol {
        self.symbol()
            .expect("called 'unwrap_sym' on a Name variant")
    }

    /// Converts this lazy symbol to an option of a symbol.
    pub fn symbol(&self) -> Option<Symbol> {
        match self {
            Self::Path(_) => None,
            Self::Sym(sym) => Some(sym.clone()),
        }
    }

    /// Get the name of the lazy symbol
    pub fn name(&self, db: &EntityDb<Symbol>) -> String {
        match self {
            Self::Path(p) => p.last().unwrap().to_string(),
            Self::Sym(s) => db.get(*s).name.clone(),
        }
    }
}

impl PrettyDump for LazySymbol {
    fn try_dump(&self, ctx: &mut PrettyCtxt) -> io::Result<()> {
        match self {
            LazySymbol::Path(path) => path.try_dump(ctx),
            LazySymbol::Sym(sym) => todo!("{sym:?}, PRETTY-DUMP WITH EXTRA CONTEXT"),
        }
    }
}

impl From<Path> for LazySymbol {
    fn from(value: Path) -> Self {
        LazySymbol::Path(value)
    }
}

impl From<Symbol> for LazySymbol {
    fn from(value: Symbol) -> Self {
        LazySymbol::Sym(value)
    }
}

#[cfg(test)]
pub mod tests {
    use super::*;

    #[test]
    fn shadowability() {
        // user-binding
        for mutability in [Mutability::Mut, Mutability::Not] {
            assert!(
                SymbolKind::UserBinding(mutability)
                    .can_shadow(&SymbolKind::UserBinding(mutability))
            );
            assert!(
                SymbolKind::UserBinding(mutability)
                    .can_shadow(&SymbolKind::UserBinding(mutability.invert()))
            );
            assert!(SymbolKind::UserBinding(mutability).can_shadow(&SymbolKind::Param));
            assert!(
                SymbolKind::UserBinding(mutability).can_shadow(&SymbolKind::GlobalDef(mutability))
            );
            assert!(
                SymbolKind::UserBinding(mutability)
                    .can_shadow(&SymbolKind::GlobalDef(mutability.invert()))
            );
            assert!(SymbolKind::UserBinding(mutability).can_shadow(&SymbolKind::Function));
            assert!(SymbolKind::UserBinding(mutability).can_shadow(&SymbolKind::Module));
        }

        // param
        assert!(SymbolKind::Param.can_shadow(&SymbolKind::UserBinding(Mutability::Mut)));
        assert!(SymbolKind::Param.can_shadow(&SymbolKind::UserBinding(Mutability::Not)));
        assert!(!SymbolKind::Param.can_shadow(&SymbolKind::Param));
        assert!(SymbolKind::Param.can_shadow(&SymbolKind::GlobalDef(Mutability::Mut)));
        assert!(SymbolKind::Param.can_shadow(&SymbolKind::GlobalDef(Mutability::Not)));
        assert!(SymbolKind::Param.can_shadow(&SymbolKind::Function));
        assert!(SymbolKind::Param.can_shadow(&SymbolKind::Module));

        // global-def
        for mutability in [Mutability::Mut, Mutability::Not] {
            assert!(
                !SymbolKind::GlobalDef(mutability).can_shadow(&SymbolKind::UserBinding(mutability))
            );
            assert!(
                !SymbolKind::GlobalDef(mutability)
                    .can_shadow(&SymbolKind::UserBinding(mutability.invert()))
            );
            assert!(!SymbolKind::GlobalDef(mutability).can_shadow(&SymbolKind::Param));
            assert!(
                !SymbolKind::GlobalDef(mutability).can_shadow(&SymbolKind::GlobalDef(mutability))
            );
            assert!(
                !SymbolKind::GlobalDef(mutability)
                    .can_shadow(&SymbolKind::GlobalDef(mutability.invert()))
            );
            assert!(!SymbolKind::GlobalDef(mutability).can_shadow(&SymbolKind::Function));
            assert!(!SymbolKind::GlobalDef(mutability).can_shadow(&SymbolKind::Module));
        }

        // function
        assert!(!SymbolKind::Function.can_shadow(&SymbolKind::UserBinding(Mutability::Mut)));
        assert!(!SymbolKind::Function.can_shadow(&SymbolKind::UserBinding(Mutability::Not)));
        assert!(!SymbolKind::Function.can_shadow(&SymbolKind::Param));
        assert!(!SymbolKind::Function.can_shadow(&SymbolKind::GlobalDef(Mutability::Mut)));
        assert!(!SymbolKind::Function.can_shadow(&SymbolKind::GlobalDef(Mutability::Not)));
        assert!(!SymbolKind::Function.can_shadow(&SymbolKind::Function));
        assert!(!SymbolKind::Function.can_shadow(&SymbolKind::Module));

        // module
        assert!(!SymbolKind::Module.can_shadow(&SymbolKind::UserBinding(Mutability::Mut)));
        assert!(!SymbolKind::Module.can_shadow(&SymbolKind::UserBinding(Mutability::Not)));
        assert!(!SymbolKind::Module.can_shadow(&SymbolKind::Param));
        assert!(!SymbolKind::Module.can_shadow(&SymbolKind::GlobalDef(Mutability::Mut)));
        assert!(!SymbolKind::Module.can_shadow(&SymbolKind::GlobalDef(Mutability::Not)));
        assert!(!SymbolKind::Module.can_shadow(&SymbolKind::Function));
        assert!(!SymbolKind::Module.can_shadow(&SymbolKind::Module));
    }
}
