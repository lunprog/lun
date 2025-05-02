use std::collections::HashMap;

use ckast::{CkChunk, FromAst};
use lun_diag::{Diagnostic, DiagnosticSink, StageResult};
use lun_parser::expr::{BinOp, UnaryOp};
use lun_parser::stmt::Chunk;
use lun_utils::Span;

pub mod ckast;

// TODO: implement a 2 pass semantic checker:
// 1. collect all of the global defs in a chunk
// 2. do the type checking of that chunk
// voilà

/// Semantic checker, ensure all of the lun's semantic is correct, it also
/// include type checking.
#[derive(Debug, Clone)]
pub struct SemanticCk {
    ast: Chunk,
    sink: DiagnosticSink,
}

impl SemanticCk {
    pub const fn new(ast: Chunk, sink: DiagnosticSink) -> SemanticCk {
        SemanticCk { ast, sink }
    }

    pub fn produce(&mut self) -> StageResult<CkChunk> {
        // 1. create the checked ast from the unchecked ast.
        let ckast = CkChunk::from_ast(self.ast.clone());
        dbg!(ckast);

        // 2. collect the global defs in the symbol table for the first block

        // 3. resolve the type of all expressions

        // 4. type check the ast and recurse at pass 2, if there is a new chunk
        todo!()
    }
}

/// Symbol
#[derive(Debug, Clone)]
pub struct Symbol {
    /// local, parameter or global
    kind: SymKind,
    /// actual type of the
    typ: Type,
    /// the name of the symbol
    name: String,
    /// which scope the symbol is referring to
    which: usize,
}

impl Symbol {
    /// Create a new symbol
    pub fn new(kind: SymKind, typ: Type, name: String, which: usize) -> Symbol {
        Symbol {
            kind,
            typ,
            name,
            which,
        }
    }

    /// Create a new local symbol
    pub fn local(typ: Type, name: String, which: usize) -> Symbol {
        Symbol {
            kind: SymKind::Local,
            typ,
            name,
            which,
        }
    }

    /// Create a new param symbol
    pub fn param(typ: Type, name: String, which: usize) -> Symbol {
        Symbol {
            kind: SymKind::Param,
            typ,
            name,
            which,
        }
    }

    /// Create a new global symbol
    pub fn global(typ: Type, name: String, which: usize) -> Symbol {
        Symbol {
            kind: SymKind::Global,
            typ,
            name,
            which,
        }
    }
}

/// Symbol type
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SymKind {
    Local,
    Param,
    Global,
}

/// Symbol type, the actual type of a symbol
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub enum Type {
    /// Unknown, at the end of type checking this type is an error.
    #[default]
    Unknown,
    /// equivalent of Rust's `i64`
    Integer,
    /// equivalent of Rust's `f64`
    Float,
    /// equivalent of Rust's `bool`, always one byte long. Can only contain
    /// `true` -> 1 and `false` -> 0
    Bool,
    /// Comptime Type, a type in the Type System.
    ///
    /// Because lun have types that are expression, types get typed checked as
    /// well. So the identifier `int` will be evaluated in EVERY expression to
    /// be of type `comptime type`.
    ComptimeType,
}

pub type SymbolMap = HashMap<String, Symbol>;

/// Symbol table.
///
/// The symbol table is a stack of hash maps. Each hashmap maps a name to a
/// symbol, the global scope is at level 0 and each scope we go deeper the
/// level increases by one.
#[derive(Debug, Clone)]
pub struct SymbolTable {
    /// all the tables, the first table is the always the global scope and as
    /// we go deeper in scopes we push new tables
    tabs: Vec<SymbolMap>,
}

impl SymbolTable {
    /// Create a new Symbol Table, with the global scope.
    pub fn new() -> SymbolTable {
        SymbolTable {
            tabs: vec![HashMap::new()],
        }
    }

    fn last_map(&self) -> &SymbolMap {
        // we can unwrap because we know there is at least the global scope.
        self.tabs.last().unwrap()
    }

    fn last_map_mut(&mut self) -> &mut SymbolMap {
        // we can unwrap because we know there is at least the global scope.
        self.tabs.last_mut().unwrap()
    }

    /// Enter a new scope
    pub fn scope_enter(&mut self) {
        self.tabs.push(SymbolMap::new())
    }

    /// Enter a new scope
    pub fn scope_exit(&mut self) {
        assert_ne!(self.tabs.len(), 1, "can't exit out of the global scope")
    }

    /// Bind a name to a symbol in the current scope
    pub fn bind(&mut self, name: String, sym: Symbol) {
        self.last_map_mut().insert(name, sym);
    }

    /// Return the current scope level
    pub fn level(&self) -> usize {
        self.tabs.len() - 1
    }

    /// Lookup for the symbol in the current scope, returns None if there is no
    /// symbol with this name in the current scope
    pub fn lookup_current(&self, name: impl AsRef<str>) -> Option<&Symbol> {
        self.last_map().get(name.as_ref())
    }

    /// Lookup for a symbol with the given name, starting at the current scope
    /// ending at the global scope, returns None if there is no symbol in any
    /// scopes
    pub fn lookup(&self, name: impl AsRef<str>) -> Option<&Symbol> {
        for i in (0..=self.level()).rev() {
            match self.tabs[i].get(name.as_ref()) {
                res @ Some(_) => return res,
                None => {}
            }
        }
        None
    }
}
