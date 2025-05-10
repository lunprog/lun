use codespan_reporting::{
    files::{self, SimpleFile},
    term::{
        self, Config,
        termcolor::{ColorChoice, StandardStream},
    },
};
use std::fmt::Display;

use lun_utils::pluralize;

pub type Diagnostic<FileId = ()> = codespan_reporting::diagnostic::Diagnostic<FileId>;
pub use codespan_reporting::diagnostic::Label;
pub use codespan_reporting::diagnostic::Severity;
pub use codespan_reporting::term::termcolor;

/// A collector of Diagnostics.
#[derive(Debug, Clone)]
pub struct DiagnosticSink {
    diags: Vec<Diagnostic<()>>,
    /// a count of all the error diagnostics
    errors: usize,
    /// a count of all the warning diagnostics
    warnings: usize,
    /// the file where diagnostics are located.
    file: SimpleFile<String, String>,
}

impl DiagnosticSink {
    pub fn new(file_name: String, source_code: String) -> DiagnosticSink {
        DiagnosticSink {
            diags: Vec::new(),
            errors: 0,
            warnings: 0,
            file: SimpleFile::new(file_name, source_code),
        }
    }

    /// Returns true if there is at least one error in the sink.
    pub fn failed(&self) -> bool {
        self.errors != 0
    }

    /// Print all diagnostics to the given writter, with default config.
    pub fn emit(&self, writer: &mut StandardStream) -> Result<(), files::Error> {
        let config = Config::default();

        for diag in &self.diags {
            term::emit(writer, &config, &self.file, diag)?;
        }

        Ok(())
    }

    /// Emit all the diagnostics to stderr.
    pub fn emit_to_stderr(&self) {
        let mut stderr = StandardStream::stderr(ColorChoice::Auto);

        self.emit(&mut stderr)
            .expect("failed to emit the diagnostics");
    }

    /// Returns a summary if there was errors or warnings, nothing if there is
    /// neither.
    pub fn summary(&self) -> Option<String> {
        if self.errors > 0 {
            Some(format!(
                "compilation of `{}` failed due to {} error{} and {} warning{}",
                self.file.name(),
                self.errors,
                pluralize(self.errors),
                self.warnings,
                pluralize(self.warnings)
            ))
        } else if self.warnings > 0 {
            Some(format!(
                "compilation of `{}` succeeded but {} warning{} emitted.",
                self.file.name(),
                self.warnings,
                pluralize(self.warnings)
            ))
        } else {
            None
        }
    }

    pub fn push(&mut self, diag: impl ToDiagnostic) {
        let diag = diag.into_diag();

        if diag.severity == Severity::Warning {
            self.warnings += 1;
        } else if diag.severity == Severity::Error {
            self.errors += 1;
        }

        self.diags.push(diag);
    }
}

/// A type that can be converted to a Diagnostic.
pub trait ToDiagnostic<FileId = ()> {
    fn into_diag(self) -> Diagnostic<FileId>;
}

impl<FileId> ToDiagnostic<FileId> for Diagnostic<FileId> {
    #[inline(always)]
    fn into_diag(self) -> Diagnostic<FileId> {
        self
    }
}

// TODO: create a cmd to explain error codes, like `lun --explain E0001`
// and it tells you what's wrong

// TODO: write the docs for ErrorCode's
/// List of all the Error Code in the lun compiling stages
#[derive(Debug, Clone, Copy)]
pub enum ErrorCode {
    /// Unknown start of token
    ///
    /// note: indetifier do not support unicode for now.
    UnknownToken = 1,
    /// Invalid digit in number: in an integer or a float
    ///
    /// Erroneus example
    /// ```lun
    /// local i = 12z34
    /// ```
    ///
    /// To fix the error, remove the wrong digit like so
    ///
    /// ```lun
    /// local i = 1234
    /// ```
    InvalidDigitNumber = 2,
    /// Too large integer literal, can't fit inside 64 bits.
    ///
    /// an integer literal must fit in 64 bits, so they must not exceed
    /// `18446744073709551615`
    TooLargeIntegerLiteral = 3,
    /// A string (") was not terminated.
    ///
    /// Erroneus example
    /// ```lun
    /// local s = "
    /// ```
    ///
    /// To fix this error, add another " add the end of your string:
    /// ```lun
    /// local s = ""
    /// ```
    UnterminatedStringLiteral = 4,
    /// Unknown character escape
    UnknownCharacterEscape = 5,
    /// Unknown character escape
    ExpectedToken = 6,
    /// Unknown character escape
    ReachedEOF = 7,
    /// Expected type
    ExpectedType = 8,
    /// Expected a type found an expression
    ExpectedTypeFoundExpr = 9,
    /// Cannot find symbol in this scope
    NotFoundInScope = 10,
    /// Call to a function require the type to be a function type
    CallRequiresFuncType = 11,
    /// Type annotations needed
    TypeAnnotationsNeeded = 12,
}

impl Display for ErrorCode {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "E{:04}", *self as usize)
    }
}

/// A custom result type to use at the end of a stage in the compiler.
///
/// In the stage you may be successful, no error, no warnings, no diagnostics,
/// then you simply return Good(T).
///
/// But if you emitted a warning or an error that was recoverable and the stage
/// was able to produce a "good" but poisoned result you should return
/// Part(T, sink).
///
/// And if the error in the stage is so bad, you just return Fail(sink).
///
/// # Why ?
///
/// Because the "simple" Result type can't carry easily the informations I want
/// to correctly handle the diagnostics.
#[derive(Debug, Clone)]
pub enum StageResult<T> {
    Good(T),
    Part(T, DiagnosticSink),
    Fail(DiagnosticSink),
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn error_code_formatting() {
        assert_eq!(String::from("E0001"), ErrorCode::UnknownToken.to_string())
    }
}
