use std::process::ExitCode;

use l2_diagnostic::{Diagnostic, StageResult};

fn main() -> ExitCode {
    match l2::run() {
        StageResult::Good(()) => ExitCode::SUCCESS,
        StageResult::Part(_, mut sink) | StageResult::Fail(mut sink) => {
            sink.push(Diagnostic::error().with_message(sink.summary().unwrap()));
            sink.emit_to_stderr();
            ExitCode::FAILURE
        }
    }
}
