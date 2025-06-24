use codespan_reporting::{
    files::{self, SimpleFile},
    term::{
        self, Config,
        termcolor::{ColorChoice, StandardStream},
    },
};
use std::fmt::Display;

use lun_utils::{Span, pluralize};

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

    /// Returns true if there is no diag, false instead.
    pub fn is_empty(&self) -> bool {
        self.diags.is_empty()
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
        } else {
            panic!("severity {:?} not supported", diag.severity);
        }

        self.diags.push(diag);
    }

    pub fn merge(&mut self, other: DiagnosticSink) {
        self.diags.extend_from_slice(&other.diags);
        self.warnings += other.warnings;
        self.errors += other.errors;
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
///
/// NOTE: until `v1.0.0` the error code may change from minor devlopement
///       versions, do not expect them to stay the same
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
    /// let i = 12z34;
    /// ```
    ///
    /// To fix the error, remove the wrong digit like so
    ///
    /// ```lun
    /// let i = 1234;
    /// ```
    InvalidDigitNumber = 2,
    /// Too large integer literal, can't fit inside 64 bits.
    ///
    /// an integer literal must fit in 64 bits, so they must not exceed
    /// `18446744073709551615`
    TooLargeIntegerLiteral = 3,
    /// A string (") was not terminated.
    ///
    /// Erroneous example
    /// ```lun
    /// let s = ";
    /// ```
    ///
    /// To fix this error, add another " add the end of your string:
    /// ```lun
    /// let s = "";
    /// ```
    UnterminatedStringLiteral = 4,
    /// Unknown character escape
    ///
    /// The character escape in the string or character literal you provided
    /// doesn't exist.
    ///
    /// Existing escapes are:
    /// ```text
    /// \0   -> 0x00
    /// \n   -> new line
    /// \r   -> carriage return
    /// \t   -> tabulation
    /// \\   -> \
    /// \xNN -> 8bit code point escape where NN are exactly two hex digits
    /// ```
    UnknownCharacterEscape = 5,
    /// Expected some token found something else.
    ///
    /// You're code isn't proper Lun syntax, you may have made a mistake or
    /// something else
    // TODO: this error code is kinda dumb fr
    ExpectedToken = 6,
    /// Reached End of file too early
    ReachedEOF = 7,
    /// Mismatched types.
    ///
    /// Erroneous code example:
    /// ```lun
    /// let a = 12;
    /// test(a);
    /// //   ^ E008: the function expected the type `bool` for the first
    /// //           argument but was provided with `int`
    ///
    /// test :: fun(a: bool) {
    ///     // ...
    /// }
    /// ```
    MismatchedTypes = 8,
    /// Expected a type found an expression
    ///
    /// You provided an expression where Lun was expecting a type.
    ///
    /// Erroneous code example:
    /// ```lun
    /// test :: fun (a: 12) {
    ///     //          ^^ E009: here Lun was expecting a type like `bool`,
    ///     //                   `isize`, `f64`, etc .. but you provided an
    ///     //                   expression `12`
    /// }
    /// ```
    ExpectedTypeFoundExpr = 9,
    /// Cannot find symbol in this scope
    ///
    /// The variable, the function or the type you provided in the current
    /// scope. You may have made a misspelling error or the type is just not in
    /// the current scope.
    ///
    /// Erroneous code example:
    /// ```lun
    /// let a = hello_world();
    /// //      ^^^^^^^^^^^ E010: `hello_world` is not in scope, Lun doesn't
    /// //                        know what you're trying to refer to.
    /// ```
    NotFoundInScope = 10,
    /// Call to a function require the type to be a function type
    ///
    /// You tried to call a function but the function operand is not a function.
    ///
    /// Erroneous code example:
    /// ```lun
    /// _ = 123("hello world");
    /// //  ^^^ E011: `123` is of type `int` you can't call an int Lun was
    /// //            expecting a function, with a type like `func(..) -> ..`
    /// ```
    CallRequiresFuncType = 11,
    /// Type annotations needed
    TypeAnnotationsNeeded = 12,
    /// `_` is a reserved identifier when you use it in a symbol's name
    ///
    /// You can't define types, functions, local and global variable with the
    /// name `_` because it's a reserved identifier, not a keyword but it is used
    /// to be able to ignore values when you don't need them like that:
    ///
    /// ```lun
    /// _ = my_function();
    ///
    /// // here `_` is assigned the result of my_function but actually the
    /// // function is just called and it's value is thrown away. You can assign
    /// // `_` multiple times with the type you want each time there is no type
    /// // checking when you assign `_` to something
    ///
    /// _ = 123;
    /// _ = true;
    /// _ = 45.6;
    /// ```
    UnderscoreReservedIdentifier = 13,
    /// `_` in expression
    UnderscoreInExpression = 14,
    /// feature not implemented
    FeatureNotImplemented = 15,
    /// loop keyword (`break` or `continue`) outside a loop.
    LoopKwOutsideLoop = 16,
    /// unknown type
    UnknownType = 17,
    /// mutation of immutable
    MutationOfImmutable = 18,
    /// name defined multiple times
    NameDefinedMultipleTimes = 19,
}

impl Display for ErrorCode {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "E{:03}", *self as usize)
    }
}
/// List of all the Warning Codes in the lun compiling stages
#[derive(Debug, Clone, Copy)]
pub enum WarnCode {
    /// A symbol is never used
    NeverUsedSymbol = 1,
}

impl Display for WarnCode {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "W{:03}", *self as usize)
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

#[macro_export]
macro_rules! tri {
    ($expr:expr, $sink:expr) => {
        match $expr {
            StageResult::Good(val) => val,
            StageResult::Part(val, sink) => {
                $sink.merge(sink);
                val
            }
            StageResult::Fail(sink) => {
                return StageResult::Fail(sink);
            }
        }
    };
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn error_code_formatting() {
        assert_eq!(String::from("E0001"), ErrorCode::UnknownToken.to_string())
    }
}

#[derive(Debug, Clone)]
pub struct FeatureNotImplemented {
    /// name of the feature
    pub feature_name: String,
    /// text under primary label
    pub label_text: String,
    /// the location of the Ast slice not implemented
    pub loc: Span,
    /// file where the feature isn't implemented
    pub compiler_file: String,
    /// line where the feature isn't implemented
    pub compiler_line: u32,
}

impl ToDiagnostic for FeatureNotImplemented {
    fn into_diag(self) -> Diagnostic<()> {
        Diagnostic::error()
            .with_code(ErrorCode::FeatureNotImplemented)
            .with_message(format!(
                "the feature {}, is not yet implemented",
                self.feature_name
            ))
            .with_label(Label::primary((), self.loc).with_message(self.label_text))
            .with_note(format!(
                "this diagnostic has been emited in file {:?} at line {}",
                self.compiler_file, self.compiler_line
            ))
    }
}

// TODO(URGENT): transform the macro to be called like that:
//
// feature_todo! {
//     feature: "MY FEATURE",
//     label: "MY LABEL",
//     loc: span(0, 0),
// }
#[macro_export]
macro_rules! feature_todo {
    {feature: $name:tt, label: $label:tt, loc: $loc:expr $( , )?} => {
        $crate::FeatureNotImplemented {
            feature_name: ($name).to_string(),
            label_text: ($label).to_string(),
            loc: $loc,
            compiler_file: ::std::file!().to_string(),
            compiler_line: ::std::line!(),
        }
    };
}
