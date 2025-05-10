use std::process::ExitCode;

use lun_diag::{Diagnostic, StageResult};

fn main() -> ExitCode {
    match lun::run() {
        StageResult::Good(()) => ExitCode::SUCCESS,
        StageResult::Part(_, mut sink) => {
            // there was only warnings
            sink.push(Diagnostic::warning().with_message(sink.summary().unwrap()));
            sink.emit_to_stderr();
            ExitCode::SUCCESS
        }
        StageResult::Fail(mut sink) => {
            sink.push(Diagnostic::error().with_message(sink.summary().unwrap()));
            sink.emit_to_stderr();
            ExitCode::FAILURE
        }
    }
}
