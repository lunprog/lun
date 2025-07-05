//! Diagnostics that may be emitted by the lexer.

use lunc_diag::{Diagnostic, ErrorCode, Label, ToDiagnostic};
use lunc_utils::Span;

#[derive(Debug, Clone)]
pub struct UnknownToken {
    pub c: char,
    pub loc: Span,
}

impl ToDiagnostic for UnknownToken {
    fn into_diag(self) -> Diagnostic<()> {
        Diagnostic::error()
            .with_code(ErrorCode::UnknownToken)
            .with_message(format!("unknown start of token: {}", self.c))
            .with_label(Label::primary((), self.loc))
    }
}

#[derive(Debug, Clone)]
pub struct InvalidDigitInNumber {
    pub c: char,
    /// location of the invalid digit
    pub loc_c: Span,
    /// location of the integer until the error
    pub loc_i: Span,
}

impl ToDiagnostic for InvalidDigitInNumber {
    fn into_diag(self) -> Diagnostic<()> {
        Diagnostic::error()
            .with_code(ErrorCode::InvalidDigitNumber)
            .with_message(format!("invalid digit in integer literal: {}", self.c))
            .with_label(Label::primary((), self.loc_c))
            .with_label(Label::secondary((), self.loc_i).with_message("in this integer"))
    }
}

#[derive(Debug, Clone)]
pub struct TooLargeIntegerLiteral {
    /// location of the too large integer to fit in 64 bits
    pub loc: Span,
}

impl ToDiagnostic for TooLargeIntegerLiteral {
    fn into_diag(self) -> Diagnostic<()> {
        Diagnostic::error()
            .with_code(ErrorCode::TooLargeIntegerLiteral)
            .with_message("integer literal is too large")
            .with_label(Label::primary((), self.loc))
            .with_note(format!("integer exceeds the limit of `{}`", u64::MAX))
    }
}

#[derive(Debug, Clone)]
pub struct UnterminatedStringLiteral {
    /// location of the unterminated string literal
    pub loc: Span,
}

impl ToDiagnostic for UnterminatedStringLiteral {
    fn into_diag(self) -> Diagnostic<()> {
        Diagnostic::error()
            .with_code(ErrorCode::UnterminatedStringLiteral)
            .with_message("unterminated string literal")
            .with_label(Label::primary((), self.loc))
    }
}

// TODO: add location of the string literal or the char literal the error is in.
#[derive(Debug, Clone)]
pub struct UnknownCharacterEscape {
    pub es: char,
    pub loc: Span,
}

impl ToDiagnostic for UnknownCharacterEscape {
    fn into_diag(self) -> Diagnostic<()> {
        Diagnostic::error()
            .with_code(ErrorCode::UnknownCharacterEscape)
            .with_message(format!("unknown character escape: {}", self.es))
            .with_label(Label::primary((), self.loc))
    }
}
