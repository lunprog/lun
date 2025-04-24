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

use std::{error::Error, time::Instant};

use crate::{
    bytecode::Blob,
    lexer::Lexer,
    parser::{AstNode, Parser, expr::Expression},
    vm::VM,
};

pub use l2_bytecode as bytecode;
pub use l2_diagnostic as diagnostic;
pub use l2_lexer as lexer;
pub use l2_parser as parser;
pub use l2_utils as utils;
pub use l2_vm as vm;

pub fn run() -> Result<(), Box<dyn Error>> {
    //     let source_code = r#"
    // fun main(args: list(string))
    //     print("Hello world!")
    // end
    //     "#;
    let source_code = r#"
1 + 1 * 9@
    "#;

    let mut lexer = Lexer::new(source_code.to_owned());

    let tt = lexer.lex()?;

    let mut parser = Parser::new(tt);

    let mut start = Instant::now();
    let ast = parser.parse()?;
    let mut elapsed = start.elapsed();

    dbg!(ast);
    println!("{elapsed:?} to parse.\n");

    let expr = Expression::parse(&mut parser)?;
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

    Ok(())
}
