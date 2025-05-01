use l2_diagnostic::DiagnosticSink;
use l2_parser::stmt::Chunk;

// TODO: implement a 2 pass semantic checker:
// 1. collect all of the global defs in a chunk
// 2. do the type checking of that chunk
// voilà

/// Type checker, ensure the type of everything are correct.
#[derive(Debug, Clone)]
pub struct SemanticCk {
    ast: Chunk,
    sink: DiagnosticSink,
}

impl SemanticCk {
    pub const fn new(ast: Chunk, sink: DiagnosticSink) -> SemanticCk {
        SemanticCk { ast, sink }
    }
}

/// Symbol
#[derive(Debug, Clone)]
pub struct Symbol {
    kind: SymKind,
    typ: SymType,
    name: String,
    which: usize,
}

/// Symbol type
#[derive(Debug, Clone)]
pub enum SymKind {
    Local,
    Param,
    Global,
}

/// Symbol type, the actual type of a symbol
#[derive(Debug, Clone)]
pub enum SymType {
    /// equivalent of Rust's `i64`
    Integer,
    /// equivalent of Rust's `f64`
    Float,
    /// equivalent of Rust's `bool`, always one byte long. Can only contain
    /// `true` -> 1 and `false` -> 0
    Bool,
    /// Comptime Type, a type in the Type System.
    ///
    /// Because l2 have types that are expression, types get typed checked as
    /// well. So the identifier `int` will be evaluated in EVERY expression to
    /// be of type `comptime type`.
    ComptimeType,
}
