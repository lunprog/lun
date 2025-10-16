//! Diagnostic reporting system for the Lun Compiler.
#![doc(
    html_logo_url = "https://raw.githubusercontent.com/lunprog/lun/main/src/assets/logo_no_bg_black.png"
)]

use codespan_reporting::{
    files::{self, Files, SimpleFile},
    term::{
        self, Config,
        termcolor::{ColorChoice, StandardStream},
    },
};

use std::{
    fmt::Display,
    panic::Location,
    sync::{Arc, RwLock},
};

use lunc_utils::{Span, pluralize};

pub type Diagnostic = codespan_reporting::diagnostic::Diagnostic<FileId>;
pub use codespan_reporting::diagnostic::Label;
pub use codespan_reporting::diagnostic::Severity;
pub use codespan_reporting::term::termcolor;
pub use lunc_utils::FileId;

type SimpFile = SimpleFile<String, String>;

#[derive(Debug, Clone)]
struct MultiFile {
    files: Vec<SimpFile>,
}

impl MultiFile {
    pub fn new() -> MultiFile {
        MultiFile { files: Vec::new() }
    }

    pub fn get(&self, id: FileId) -> &SimpFile {
        self.files.get(id.as_usize()).expect("unknown file id.")
    }
}

impl<'a> Files<'a> for MultiFile {
    type FileId = FileId;
    // TODO: maybe change the Name to PathBug instead of String at some point
    type Name = String;
    type Source = &'a str;

    fn name(&'a self, id: Self::FileId) -> Result<Self::Name, files::Error> {
        Ok(self.get(id).name().clone())
    }

    fn source(&'a self, id: Self::FileId) -> Result<Self::Source, files::Error> {
        Ok(self.get(id).source().as_str())
    }

    fn line_index(&'a self, id: Self::FileId, byte_index: usize) -> Result<usize, files::Error> {
        self.get(id).line_index((), byte_index)
    }

    fn line_range(
        &'a self,
        id: Self::FileId,
        line_index: usize,
    ) -> Result<std::ops::Range<usize>, files::Error> {
        self.get(id).line_range((), line_index)
    }
}
/// A collector of Diagnostics.
#[derive(Debug, Clone)]
pub struct DiagnosticSink(Arc<RwLock<SinkInner>>);

impl DiagnosticSink {
    /// Create a new diagnostic sink
    pub fn new(debug: bool) -> DiagnosticSink {
        DiagnosticSink(Arc::new(RwLock::new(SinkInner::new(debug))))
    }

    /// Registers a new file into the diagnostic sink and returns the correspond file id.
    pub fn register_file(&self, name: String, source: String) -> FileId {
        let mut inner = self.0.write().unwrap();
        inner.register_file(name, source)
    }

    /// Returns true if there is at least one error in the sink.
    pub fn failed(&self) -> bool {
        let inner = self.0.read().unwrap();
        inner.failed()
    }

    /// Returns true if there is no diag, false instead.
    pub fn is_empty(&self) -> bool {
        let inner = self.0.read().unwrap();
        inner.is_empty()
    }

    /// Print all diagnostics to the given writer, with default config.
    pub fn dump_with(&self, writer: &mut StandardStream) -> Result<(), files::Error> {
        let inner = self.0.read().unwrap();
        inner.dump_with(writer)
    }

    /// Emit all the diagnostics to stderr.
    pub fn dump(&self) {
        let inner = self.0.read().unwrap();
        inner.dump_to_stderr();
    }

    /// Returns a summary if there was errors or warnings, nothing if there is
    /// neither.
    pub fn summary(&self, orb_name: &str) -> Option<String> {
        let inner = self.0.read().unwrap();
        inner.summary(orb_name)
    }

    /// Emit a diagnostic
    #[track_caller]
    pub fn emit(&mut self, diag: impl ToDiagnostic) -> DiagGuaranteed {
        let mut inner = self.0.write().unwrap();
        inner.emit(diag);

        DiagGuaranteed(())
    }

    /// Emit a summary diagnostic
    pub fn emit_summary(&mut self, orb_name: &str) {
        {
            let mut inner = self.0.write().unwrap();
            inner.debug = false;
        }

        self.emit(
            if self.failed() {
                Diagnostic::error()
            } else {
                Diagnostic::warning()
            }
            .with_message(self.summary(orb_name).unwrap()),
        );
    }

    /// Return the name of the current file
    pub fn name(&self, fid: FileId) -> Option<String> {
        let inner = self.0.read().unwrap();

        inner.files.name(fid).ok()
    }
}

/// A collector of Diagnostics.
#[derive(Debug, Clone)]
struct SinkInner {
    diags: Vec<Diagnostic>,
    /// a count of all the error diagnostics
    errors: usize,
    /// a count of all the warning diagnostics
    warnings: usize,
    /// the file where diagnostics are located.
    files: MultiFile,
    /// last file id given
    last_fid: u32,
    /// does we add debug information to the output?
    debug: bool,
}

impl SinkInner {
    /// Create a new diagnostic sink
    pub fn new(debug: bool) -> SinkInner {
        SinkInner {
            diags: Vec::new(),
            errors: 0,
            warnings: 0,
            files: MultiFile::new(),
            last_fid: 0,
            debug,
        }
    }

    /// Registers a new file into the diagnostic sink and returns the correspond file id.
    pub fn register_file(&mut self, name: String, source: String) -> FileId {
        let fid = FileId::new(self.last_fid);
        self.last_fid += 1;

        self.files.files.push(SimpleFile::new(name, source));
        fid
    }

    /// Returns true if there is at least one error in the sink.
    pub fn failed(&self) -> bool {
        self.errors != 0
    }

    /// Returns true if there is no diag, false instead.
    pub fn is_empty(&self) -> bool {
        self.diags.is_empty()
    }

    /// Print all diagnostics to the given writer, with default config.
    pub fn dump_with(&self, writer: &mut StandardStream) -> Result<(), files::Error> {
        let config = Config::default();

        for diag in &self.diags {
            term::emit(writer, &config, &self.files, diag)?;
        }

        Ok(())
    }

    /// Emit all the diagnostics to stderr.
    pub fn dump_to_stderr(&self) {
        let mut stderr = StandardStream::stderr(ColorChoice::Auto);

        self.dump_with(&mut stderr)
            .expect("failed to emit the diagnostics");
    }

    /// Returns a summary if there was errors or warnings, nothing if there is
    /// neither.
    pub fn summary(&self, orb_name: &str) -> Option<String> {
        if self.errors > 0 {
            Some(format!(
                "compilation of `{}` failed due to {} error{} and {} warning{}",
                orb_name,
                self.errors,
                pluralize(self.errors),
                self.warnings,
                pluralize(self.warnings)
            ))
        } else if self.warnings > 0 {
            Some(format!(
                "compilation of `{}` succeeded but {} warning{} emitted.",
                orb_name,
                self.warnings,
                pluralize(self.warnings)
            ))
        } else {
            None
        }
    }

    #[track_caller]
    pub fn emit(&mut self, diag: impl ToDiagnostic) {
        let mut diag = diag.into_diag();

        if diag.severity == Severity::Warning {
            self.warnings += 1;
        } else if diag.severity == Severity::Error {
            self.errors += 1;
        } else {
            panic!("severity '{:?}' is not supported", diag.severity);
        }

        if self.debug {
            let caller_loc = Location::caller();
            diag.notes.push(format!(
                "DEBUG: this diagnostic was emitted in {file}, at {line}:{column}",
                file = caller_loc.file(),
                line = caller_loc.line(),
                column = caller_loc.column()
            ));
        }

        self.diags.push(diag);
    }
}

/// A type that can be converted to a Diagnostic.
pub trait ToDiagnostic {
    fn into_diag(self) -> Diagnostic;
}

impl ToDiagnostic for Diagnostic {
    #[inline(always)]
    fn into_diag(self) -> Diagnostic {
        self
    }
}

// TODO: create a cmd to explain error codes, like `lun --explain E0001`
// and it tells you what's wrong

// TODO: write the docs for ErrorCode's

/// List of all the Error Code in the lun compiling stages
///
/// # Testing
///
/// Diagnostic emission are tested to ensure the compiler keeps the same
/// behavior and to test the UI of the diagnostics as a secondary benefit. The
/// tests are located in those files:
///
/// | Code | Test path(s)                                      |
/// |------|---------------------------------------------------|
/// |`E001`| `tests/lexer/E001.lun`                            |
/// |`E002`| `tests/lexer/E002.lun`[^1]                        |
/// |`E003`| `tests/lexer/E003.lun`[^2]                        |
/// |`E004`| `tests/lexer/E004.lun`                            |
/// |`E005`| `tests/lexer/E005.lun`                            |
/// |`E006`| `tests/parser/E006_<ast node>[_nth].lun`          |
/// |`E007`| n/a[^3]                                           |
/// |`E008`| `tests/scir/E008.lun`                             |
/// |`E009`| `tests/scir/E009.lun`                             |
/// |`E010`| `tests/lexer/E010.lun` <br> `tests/lexer/bim.lun` |
/// |`E011`| `tests/scir/E011.lun`                             |
/// |`E012`| n/a[^4]                                           |
/// |`E013`| `tests/lexer/E013.lun`                            |
/// |`E014`| `tests/lexer/E014.lun`                            |
/// |`E015`| n/a[^5]                                           |
/// |`E016`| `tests/scir/E016.lun`                             |
/// |`E017`| deprecated, **CAN BE REPLACED BY A NEW CODE**     |
/// |`E018`| deprecated, **CAN BE REPLACED BY A NEW CODE**     |
/// |`E019`| `tests/lexer/E019.lun`                            |
/// |`E020`| `tests/lexer/E020.lun`                            |
/// |`E021`| `tests/lexer/E021.lun`                            |
/// |`E022`| `tests/lexer/E022.lun`                            |
/// |`E023`| `tests/lexer/E023.lun`                            |
/// |`E024`| `tests/lexer/E024.lun`                            |
/// |`E025`| `tests/lexer/E025.lun`                            |
/// |`E026`| `tests/lexer/E026.lun`                            |
/// |`E027`| `tests/scir/E027.lun`                             |
/// |`E028`| `tests/scir/E028.lun`                             |
/// |`E029`| `tests/scir/E029.lun`                             |
/// |`E030`| `tests/scir/E030.lun`                             |
/// |`E031`| `tests/scir/E031.lun`                             |
/// |`E032`| `tests/scir/E032.lun`                             |
/// |`E033`| `tests/scir/E033.lun`                             |
/// |`E034`| `tests/scir/E034.lun`                             |
/// |`E035`| `tests/parser/E035_1.lun`,                        |
/// |  ^   | `tests/parser/E035_2.lun`,                        |
/// |  ^   | `tests/parser/E035_3.lun`                         |
/// |`E036`| `tests/scir/E036.lun`                             |
/// |`E037`| `tests/scir/E037.lun`                             |
/// |`E038`| `tests/parser/E038.lun`                           |
/// |`E039`| `tests/scir/E039.lun`                             |
/// |`E040`| `tests/scir/E040.lun`                             |
/// |`E041`| `tests/behavior/E041.lun`                         |
/// |`E042`| `tests/behavior/E042.lun`                         |
///
/// # Note
///
/// until `v1.0.0` the error code may change from minor devlopement versions, do
/// not expect them to stay the same
///
/// [^1]: this diagnostic is technically emitted only when you have an invalid
///       digit inside of an hexadecimal escape because when we lex numbers (int
///       / float) we are only converting a string that contains only numeric
///       characters.
/// [^2]: only tested in integer literal, not tested inside float literals,
///       and can never occur in hex escape because we are taking the next
///       2 characters.
/// [^3]: in theory this diag is emitted in the parser when there is no more
///       token in the token stream, but the token stream guarantees that there
///       is an EOF token at the end, so this diag is never truly emitted.
/// [^4]: this diag is never truly emitted, because we try to use dummy types
///       as much as possible when we encounter an error so there is no testing
///       for it.
/// [^5]: useless to test that a feature isn't implemented in my opinion
#[derive(Debug, Clone, Copy)]
pub enum ErrorCode {
    /// Unknown start of token
    ///
    /// note: indetifier do not support unicode for now.
    ///
    /// # Testing
    ///
    /// `tests/lexer/E001.lun`
    UnknownToken = 1,
    /// Invalid digit in number: in an integer or a float
    ///
    /// Erroneous example
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
    /// Too large integer literal, can't fit inside 128 bits.
    ///
    /// an integer literal must fit in 64 bits, so they must not exceed
    /// `340_282_366_920_938_463_463_374_607_431_768_211_455`
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
    /// \0       -> 0x00, null
    /// \n       -> 0x0A, line feed
    /// \r       -> 0x0D, carriage return
    /// \f       -> 0x0C, form feed
    /// \t       -> 0x09, (horizontal) tabulation
    /// \v       -> 0x0B, vertical tabulation
    /// \a       -> 0x07, alert / bell
    /// \b       -> 0x08, backspace
    /// \e       -> 0x1B, escape [ESC]
    /// \\       -> `\`
    /// \xNN     -> 0xNN
    /// \u{NN..} -> 0xNN..
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
    /// label keywords (`break` or `continue`) outside of a loop or block.
    LabelKwOutsideLoopOrBlock = 16,
    /// unknown type
    #[deprecated(note = "pls replace me")]
    UnknownType = 17,
    /// mutation of immutable
    #[deprecated(note = "pls replace me")]
    MutationOfImmutable = 18,
    /// name defined multiple times
    NameDefinedMultipleTimes = 19,
    /// expected exponent part of hexadecimal floating point literal
    ExpectedExponentPart = 20,
    /// no digits where found after a number base
    NoDigitsInANonDecimal = 21,
    /// too many codepoints in a character literal, can only contain one codepoint
    TooManyCodepointsInCharLiteral = 22,
    /// empty character literal, expected one codepoint found zero
    EmptyCharLiteral = 23,
    /// not enough hexadecimal digits in escape sequence
    NotEnoughHexDigits = 24,
    /// invalid unicode escape
    InvalidUnicodeEscape = 25,
    /// file for module does not exist
    ModuleFileDoesnotExist = 26,
    /// expected the expression to be a place expression.
    ///
    /// # Definition
    ///
    /// A place expression, is an expression that represents a memory location,
    /// like a local / global variable / definition that is mutable, a
    /// dereference expression.
    ExpectedPlaceExpression = 27,
    /// the amount of arguments passed to a function call does not match the
    /// amount the function was defined with.
    ArityDoesntMatch = 28,
    /// cannot resolve the provided expression at compile time.
    CantResolveComptimeValue = 29,
    /// use of an undefined label.
    UseOfUndefinedLabel = 30,
    /// a break inside of a labeled block without a label.
    BreakUseAnImplicitLabelInBlock = 31,
    /// a block cannot be continued.
    CantContinueABlock = 32,
    /// break from a predicate or iterator loop with a value, it is only
    /// supported inside a labeled block or an infinite loop.
    BreakWithValueUnsupported = 33,
    /// a literal expression is overflowing
    OverflowingLiteral = 34,
    /// unknown directive
    UnknownDirective = 35,
    /// borrowed as mutable, but was not defined as mutable
    BorrowMutWhenNotDefinedMut = 36,
    /// function declaration outside of an extern block
    OutsideExternBlock = 37,
    /// unknown abi
    UnknownAbi = 38,
    /// item not allowed inside an extern block
    ItemNotAllowedInExternBlock = 39,
    /// cannot have a function definition / declaration inside of a global
    /// mutable definition
    FunctionInGlobalMut = 40,
    /// main function isn't defined in a binary orb type.
    MainUndefined = 41,
    /// bad main function signature.
    BadMainSignature = 42,
    // NOTE: **BEFORE ADDING A NEW ERROR CODE, the `E017` and `E018` should be replaced!**
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
    /// Unreachable code
    UnreachableCode = 2,
    /// unused label
    UnusedLabel = 3,
}

impl Display for WarnCode {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "W{:03}", *self as usize)
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
    fn into_diag(self) -> Diagnostic {
        Diagnostic::error()
            .with_code(ErrorCode::FeatureNotImplemented)
            .with_message(format!(
                "the feature '{}', is not yet implemented",
                self.feature_name
            ))
            .with_label(Label::primary(self.loc.fid, self.loc).with_message(self.label_text))
            .with_note(format!(
                "this diagnostic has been emitted in file {:?} at line {}",
                self.compiler_file, self.compiler_line
            ))
    }
}

#[macro_export]
macro_rules! feature_todo {
    {feature: $name:tt, label: $label:tt, loc: $loc:expr $( , )?} => {
        lunc_diag::ToDiagnostic::into_diag($crate::FeatureNotImplemented {
            feature_name: ($name).to_string(),
            label_text: ($label).to_string(),
            loc: $loc,
            compiler_file: ::std::file!().to_string(),
            compiler_line: ::std::line!(),
        })
    };
}

#[derive(Debug, Clone)]
pub struct ReachedEOF {
    pub loc: Span,
}

impl ToDiagnostic for ReachedEOF {
    fn into_diag(self) -> Diagnostic {
        Diagnostic::error()
            .with_code(ErrorCode::ReachedEOF)
            .with_message("reached end of file too early")
            .with_label(Label::primary(self.loc.fid, self.loc))
    }
}

/// Diagnostic was guaranteed to be reported to the user.
#[derive(Debug, Clone)]
pub struct DiagGuaranteed(pub(crate) ());

/// Internal result, used by functions that output something that can produce a
/// diagnostic and cannot recover from it.
pub type IResult<T> = core::result::Result<T, Diagnostic>;

/// Extension to [`Result`].
pub trait ResultExt<T>: private::Sealed {
    fn unwrap_and_emit(self, sink: &mut DiagnosticSink) -> T;
}

impl<T: Default> ResultExt<T> for IResult<T> {
    fn unwrap_and_emit(self, sink: &mut DiagnosticSink) -> T {
        match self {
            Ok(p) => p,
            Err(d) => {
                sink.emit(d);

                T::default()
            }
        }
    }
}

mod private {
    pub trait Sealed {}

    impl<T, E> Sealed for Result<T, E> {}
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn error_code_formatting() {
        assert_eq!(String::from("E001"), ErrorCode::UnknownToken.to_string())
    }
}
