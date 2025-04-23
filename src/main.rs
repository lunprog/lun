use std::{error::Error, process::ExitCode, time::Instant};

use l2::{blob::Blob, lexer::Lexer, vm::VM};

fn run() -> Result<(), Box<dyn Error>> {
    let source_code = r#"
fun main(args: list(string))
    print("Hello world!")
end
    "#;

    let mut lexer = Lexer::new(source_code.to_owned());

    let mut start = Instant::now();

    let tt = lexer.lex()?;

    let mut elapsed = start.elapsed();

    // dbg!(tt);
    println!("{elapsed:?} to lex.\n");

    let mut blob = Blob::new();

    let _ = blob.dpool.write_integer(0xDEADBEEF);
    blob.write_const(0, size_of::<u64>() as u16);

    blob.write_return();

    blob.disassemble("test blob");

    let mut vm = VM::new(blob);
    start = Instant::now();

    let res = vm.run();

    elapsed = start.elapsed();

    println!("{elapsed:?} to run.\n");
    println!("RES = {:X?}", res);

    Ok(())
}

fn main() -> ExitCode {
    match run() {
        Ok(()) => ExitCode::SUCCESS,
        Err(e) => {
            eprintln!("ERROR: {e}");
            ExitCode::FAILURE
        }
    }
}
