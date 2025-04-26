use l2_diagnostic::DiagnosticSink;
use l2_parser::stmt::Chunk;

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
