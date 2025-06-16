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
    bc::{AFunct, BcBlob, Reg},
    diag::{DiagnosticSink, StageResult, tri},
    lexer::Lexer,
    parser::Parser,
    semack::SemanticCk,
    vm::Vm,
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
    let source_code = include_str!("../examples/forward_use.lun");

    // 1. create the sink
    let mut sink = DiagnosticSink::new("examples.lun".to_owned(), source_code.to_owned());

    // 2. lex the source code to tokens
    let mut lexer = Lexer::new(sink.clone(), source_code.to_owned());

    let tt = tri!(lexer.produce(), sink);

    // 3. parse the token tree to an ast
    let mut parser = Parser::new(tt, sink.clone());

    let ast = tri!(parser.produce(), sink);

    // 4. semantic and type checking of the ast

    let mut semacker = SemanticCk::new(ast, sink.clone());

    let ckast = tri!(semacker.produce(), sink);

    dbg!(&ckast);

    // TODO: make the codegenerator work on the ir.

    let mut blob = BcBlob::new();
    blob.write_add(AFunct::X, Reg::t1, Reg::a0, Reg::a1);

    blob.write_mul(AFunct::F16, Reg::a0, Reg::t1, Reg::a2);

    blob.write_call(0xDEAD_BEEF);

    blob.write_ret();

    blob.write_call(0xDEAD_BEEF);

    blob.write_jze(Reg::sp, 0xDEAD, Reg::a0);
    blob.write_jze(Reg::sp, 0xDEAD, Reg::zr);

    blob.write_beq(Reg::a0, Reg::zr, 0xBEEF);

    blob.write_ld_b(Reg::t1, 0x4, Reg::sp);

    blob.write_st_b(Reg::t1, 0x4, Reg::sp);
    blob.write_st_h(Reg::t1, 0x4, Reg::sp);
    blob.write_st_w(Reg::t1, 0x4, Reg::sp);
    blob.write_st_d(Reg::t1, 0x4, Reg::sp);

    blob.write_li_b(Reg::t2, 0xFF, Reg::a1);
    blob.write_li_h(Reg::t2, 0xFF00, Reg::a1);
    blob.write_li_w(Reg::t2, 0xFF0000, Reg::a1);
    blob.write_li_d(Reg::t2, 0xDEAD_BEEF, Reg::a1);
    blob.disassemble("test blob");

    let mut vm = Vm::new(Vm::BASE_STACK, blob);
    vm.debug_regs();
    vm.run();

    // 6. code generation
    // let mut codegen = CodeGenerator::new(ckast, sink.clone(), LBType::Exec);
    // let lb = tri!(codegen.produce(), sink);

    // let mut file = File::create("test.lb").unwrap();
    // lb.serialize(&mut file).unwrap();

    // lb.dump();

    // THE VM PARTS

    // let mut blob = BcBlob::new();

    // let a = blob.dpool.write_integer(10) as u32;
    // blob.write_const(a);
    // let b = blob.dpool.write_integer(4) as u32;
    // dbg!(&blob.dpool);
    // blob.write_const(b);

    // blob.write_sub();

    // blob.write_return();

    // blob.disassemble("test blob");

    // let mut vm = VM::new(blob);

    // let res = vm.run();

    // println!("RES = {}", res);

    if sink.is_empty() {
        StageResult::Good(())
    } else {
        StageResult::Part((), sink)
    }
}
