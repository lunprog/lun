//! Contains the [ModuleTree], and everything related to the metadata added inside of a `llib` orb type.
#![doc(
    html_logo_url = "https://raw.githubusercontent.com/lunprog/lun/main/src/assets/logo_no_bg_black.png"
)]

use std::collections::HashMap;

use lunc_utils::symbol::{EffectivePath, LazySymbol, SymKind, Symbol};

pub mod meta;

/// A tree representing the orb definitions as a tree
#[derive(Debug, Clone)]
pub struct ModuleTree {
    /// submodules of this module
    submodules: HashMap<String, ModuleTree>,
    /// definitions in this module tree, a definition can only be one of:
    /// - global
    /// - function
    defs: HashMap<String, Symbol>,
    /// is this module tree the root module?
    root_name: Option<String>,
    /// symbol of the module
    pub sym: LazySymbol,
}

impl ModuleTree {
    /// Creates a new ModuleTree, set `root_name` arg to None if the ModuleTree
    /// you want to create is not the root module of the orb.
    pub fn new(root_name: Option<String>, sym: LazySymbol) -> ModuleTree {
        ModuleTree {
            submodules: HashMap::default(),
            defs: HashMap::new(),
            root_name,
            sym,
        }
    }

    /// Get the submodule of the current module with `name`.
    pub fn submod(&self, name: impl AsRef<str>) -> Option<&ModuleTree> {
        self.submodules.get(name.as_ref())
    }

    /// Mutable get the submodule of the current module with `name`.
    pub fn submod_mut(&mut self, name: impl AsRef<str>) -> Option<&mut ModuleTree> {
        self.submodules.get_mut(name.as_ref())
    }

    /// Define a new symbol inside the current module tree
    pub fn define(&mut self, name: String, sym: Symbol) {
        assert!(matches!(
            sym.kind(),
            SymKind::Global { .. } | SymKind::Function
        ));

        self.defs.insert(name, sym.clone());
    }

    /// Define a new module in the current module tree
    pub fn define_mod(&mut self, name: String, symref: Symbol) {
        self.submodules
            .insert(name.clone(), ModuleTree::new(None, LazySymbol::Sym(symref)));
    }

    /// Is this module the root module of the orb?
    #[inline]
    pub fn is_root(&self) -> bool {
        self.root_name.is_some()
    }

    /// If self is root module, get the submodule at the `path` and returns it,
    /// or returns None if the path does not lead to anything
    pub fn goto(&self, path: &EffectivePath) -> Option<&ModuleTree> {
        assert!(self.is_root());

        let mut iterator = path.as_slice().iter();

        let Some("orb") = iterator.next().map(|s| s.as_str()) else {
            return None;
        };

        let mut current_module = self;

        for member in iterator {
            current_module = current_module.submod(member)?;
        }

        Some(current_module)
    }

    /// If self is root module, get the submodule at the `path` and returns it,
    /// or returns None if the path does not lead to anything
    pub fn goto_mut(&mut self, path: &EffectivePath) -> Option<&mut ModuleTree> {
        assert!(self.is_root());

        let mut iterator = path.as_slice().iter();

        let Some("orb") = iterator.next().map(|s| s.as_str()) else {
            return None;
        };

        let mut current_module = self;

        for member in iterator {
            current_module = current_module.submod_mut(member)?;
        }

        Some(current_module)
    }

    /// Get a definition in the current module tree
    pub fn def(&self, name: impl AsRef<str>) -> Option<Symbol> {
        self.defs.get(name.as_ref()).cloned()
    }

    /// Returns the symbol of the definition or the module with this name
    pub fn def_or_mod(&self, name: impl AsRef<str>) -> Option<Symbol> {
        self.def(&name)
            .or(self.submod(&name).map(|submod| submod.sym.unwrap_sym()))
    }

    /// Gets the name of the root module if any.
    pub fn root_name(&self) -> Option<&str> {
        self.root_name.as_deref()
    }
}
