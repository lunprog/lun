use std::io::Write;
use std::process::ExitCode;

use termcolor::{Color, ColorSpec, StandardStream, WriteColor};

use lunc::{CliError::BuildDiagnostics, flush_outs};

fn main() -> ExitCode {
    let mut out = StandardStream::stderr(termcolor::ColorChoice::Auto);

    match lunc::run() {
        Ok(()) => {
            flush_outs();

            ExitCode::SUCCESS
        }
        Err(BuildDiagnostics { failed }) => {
            flush_outs();

            if failed {
                lunc::exit_code_compilation_failed()
            } else {
                ExitCode::SUCCESS
            }
        }
        Err(e) => {
            out.set_color(ColorSpec::new().set_bold(true)).unwrap();
            write!(out, "lunc: ").unwrap();
            out.set_color(ColorSpec::new().set_fg(Some(Color::Red)).set_bold(true))
                .unwrap();
            write!(out, "error: ").unwrap();
            out.reset().unwrap();
            writeln!(out, "{e}").unwrap();

            flush_outs();

            ExitCode::FAILURE
        }
    }
}
