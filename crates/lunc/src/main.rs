use std::io::Write;
use std::process::ExitCode;

use lunc_diag::Diagnostic;
use termcolor::{Color, ColorSpec, StandardStream, WriteColor};

use lunc::CliError::CompilerDiagnostics;

fn main() -> ExitCode {
    let mut out = StandardStream::stderr(termcolor::ColorChoice::Auto);

    match lunc::run() {
        Ok(()) => ExitCode::SUCCESS,
        Err(CompilerDiagnostics { mut sink, orb_name }) => {
            sink.push(
                if sink.failed() {
                    Diagnostic::error()
                } else {
                    Diagnostic::warning()
                }
                .with_message(sink.summary(&orb_name).unwrap()),
            );

            sink.emit_to_stderr();

            if sink.failed() {
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

            ExitCode::FAILURE
        }
    }
}
