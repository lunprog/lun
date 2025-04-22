use std::error::Error;

use k2::lexer::Lexer;

fn main() -> Result<(), Box<dyn Error>> {
    let source_code = r#"
fun main(args: list(string))
    print("Hello world!")
end
    "#;

    let mut lexer = Lexer::new(source_code.to_owned());
    let tt = lexer.lex()?;
    dbg!(tt);

    Ok(())
}
