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
    bc::Blob,
    diag::{DiagnosticSink, StageResult},
    lexer::Lexer,
    parser::Parser,
    semack::SemanticCk,
    vm::VM,
};

pub use lun_bc as bc;
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
    let source_code = include_str!("../examples/function.lun");

    // 1. create the sink
    let sink = DiagnosticSink::new("examples.lun".to_owned(), source_code.to_owned());

    // 2. lex the source code to tokens
    let mut lexer = Lexer::new(sink.clone(), source_code.to_owned());

    let tt = match lexer.produce() {
        StageResult::Good(tt) => tt,
        StageResult::Part(_, sink) => {
            return StageResult::Fail(sink);
        }
        StageResult::Fail(sink) => {
            return StageResult::Fail(sink);
        }
    };

    // 3. parse the token tree to an ast
    let mut parser = Parser::new(tt, sink.clone());

    let ast = match parser.produce() {
        StageResult::Good(ast) => ast,
        StageResult::Part(_, sink) => {
            return StageResult::Fail(sink);
        }
        StageResult::Fail(sink) => {
            return StageResult::Fail(sink);
        }
    };

    // 4. semantic and type checking of the ast

    dbg!(&ast);
    let mut semacker = SemanticCk::new(ast, sink.clone());

    let ckast = match semacker.produce() {
        StageResult::Good(ast) => ast,
        StageResult::Part(_, sink) => {
            return StageResult::Fail(sink);
        }
        StageResult::Fail(sink) => {
            return StageResult::Fail(sink);
        }
    };

    dbg!(&ckast);

    // THE VM PARTS

    let mut blob = Blob::new();

    let a = blob.dpool.write_integer(10) as u32;
    blob.write_const(a, size_of::<i64>() as u16);
    let b = blob.dpool.write_integer(4) as u32;
    blob.write_const(b, size_of::<i64>() as u16);

    blob.write_sub();

    blob.write_return();

    blob.disassemble("test blob");

    let mut vm = VM::new(blob);

    let res = vm.run();

    println!("RES = {}", res);

    StageResult::Good(())
}
