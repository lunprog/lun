//! Parsing of l2's statements and chunk.

use super::*;

/// Every source file is a Chunk, a Chunk is a sequence of Statements
#[derive(Debug, Clone)]
pub struct Chunk {
    pub stmts: Vec<Statement>,
    pub loc: Span,
}

impl AstNode for Chunk {
    fn parse(parser: &mut Parser) -> Result<Self, Diagnostic> {
        _ = parser;
        todo!("chunk parsing :D")
    }
}

/// A l2 statement
#[derive(Debug, Clone)]
pub struct Statement {
    pub stmt: StmtKind,
    pub loc: Span,
}

#[derive(Debug, Clone)]
pub enum StmtKind {
    Assignement { variable: String, value: Expression },
}
