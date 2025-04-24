//! L2 is a simple, staticaly typed programming language that aims to replace Lua,
//!
//! # Hello world example
//!
//! ```l2
//! println("Hello world!")
//! ```
//!
//! # Fibonacci example
//!
//! ```l2
//! fun fib(n: int) -> int
//!     if n < 2 then return n end
//!     return fib(n - 1) + fib(n + 1)
//! end
//! ```

use std::time::Instant;

use crate::{
    bytecode::Blob,
    diagnostic::DiagnosticSink,
    lexer::Lexer,
    parser::{AstNode, Parser, expr::Expression},
    vm::VM,
};

pub use l2_bytecode as bytecode;
pub use l2_diagnostic as diagnostic;
use l2_diagnostic::StageResult;
pub use l2_lexer as lexer;
pub use l2_parser as parser;
pub use l2_utils as utils;
use l2_utils::token::TokenTree;
pub use l2_vm as vm;

// TODO: add a panic hook to tell that if l2 had panicked it's a bug an it
// should be reported.
pub fn run() -> StageResult<()> {
    // let source_code = r#"
    // fun main(args: list(string))
    //     print("Hello world!")
    // end
    //     "#;
    let source_code = r#"
1 + 1 * 93# = 1844674407370955161d5 "BLAH BLAH BLAH\xAW"
        "#;

    let mut sink = DiagnosticSink::new("test.l2".to_owned(), source_code.to_owned());

    let mut lexer = Lexer::new(sink.clone(), source_code.to_owned());

    let tt = match lexer.produce() {
        StageResult::Good(tt) => tt,
        StageResult::Part(tt, new_sink) => {
            sink = new_sink;
            tt
        }
        StageResult::Fail(new_sink) => {
            sink = new_sink;
            TokenTree::new()
        }
    };

    if sink.failed() {
        return StageResult::Fail(sink);
    }

    let mut parser = Parser::new(tt);

    let mut start = Instant::now();
    let ast = parser.parse().unwrap();
    let mut elapsed = start.elapsed();

    dbg!(ast);
    println!("{elapsed:?} to parse.\n");

    let expr = Expression::parse(&mut parser).unwrap();
    dbg!(expr);

    let mut blob = Blob::new();

    let a = blob.dpool.write_integer(10) as u32;
    blob.write_const(a, size_of::<i64>() as u16);
    let b = blob.dpool.write_integer(4) as u32;
    blob.write_const(b, size_of::<i64>() as u16);

    blob.write_sub();

    blob.write_return();

    blob.disassemble("test blob");

    let mut vm = VM::new(blob);
    start = Instant::now();

    let res = vm.run();

    elapsed = start.elapsed();

    println!("{elapsed:?} to run.\n");
    println!("RES = {}", res);

    StageResult::Good(())
}
