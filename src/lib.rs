//! Lun is a simple, staticaly typed programming language heavily inspired by
//! Lua.
//!
//! # Hello world example
//!
//! ```lun
//! println("Hello world!")
//! ```
//!
//! # Fibonacci example
//!
//! ```lun
//! fun fib(n: int) -> int
//!     if n < 2 then return n end
//!     return fib(n - 1) + fib(n + 1)
//! end
//! ```

use crate::{
    diag::{DiagnosticSink, StageResult, tri},
    lexer::Lexer,
    parser::Parser,
    semack::SemanticCk,
};

pub use lun_bc as bc;
pub use lun_codegen as codegen;
pub use lun_diag as diag;
pub use lun_lexer as lexer;
pub use lun_parser as parser;
pub use lun_semack as semack;
pub use lun_utils as utils;
pub use lun_vm as vm;

// TODO: add a panic hook to tell that if lun had panicked it's a bug an it
// should be reported.
pub fn run() -> StageResult<()> {
    // 0. retrieve the source code
    // let source_code = include_str!("../examples/forward_use.lun");
    let source_code = include_str!("../test.lun");

    // 1. create the sink
    let mut sink = DiagnosticSink::new("examples.lun".to_owned(), source_code.to_owned());

    // 2. lex the source code to tokens
    let mut lexer = Lexer::new(sink.clone(), source_code.to_owned());

    let tt = tri!(lexer.produce(), sink);

    // 3. parse the token tree to an ast
    let mut parser = Parser::new(tt, sink.clone());

    let program = tri!(parser.produce(), sink);

    // 4. semantic and type checking of the ast

    let mut semacker = SemanticCk::new(program, sink.clone());

    let ckprogram = tri!(semacker.produce(), sink);
    dbg!(ckprogram);

    if sink.is_empty() {
        StageResult::Good(())
    } else {
        StageResult::Part((), sink)
    }
}
