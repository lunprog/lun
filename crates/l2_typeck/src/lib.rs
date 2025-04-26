use l2_diagnostic::DiagnosticSink;
use l2_parser::stmt::Chunk;

/// Type checker, ensure the type of everything are correct.
#[derive(Debug, Clone)]
pub struct TypeChecker {
    ast: Chunk,
    sink: DiagnosticSink,
}
