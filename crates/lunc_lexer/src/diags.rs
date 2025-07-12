//! Diagnostics that may be emitted by the lexer.

use lunc_diag::{Diagnostic, ErrorCode, Label, ToDiagnostic};
use lunc_utils::Span;

#[derive(Debug, Clone)]
pub struct UnknownToken {
    pub c: char,
    pub loc: Span,
}

impl ToDiagnostic for UnknownToken {
    fn into_diag(self) -> Diagnostic {
        Diagnostic::error()
            .with_code(ErrorCode::UnknownToken)
            .with_message(format!("unknown start of token: {}", self.c))
            .with_label(Label::primary(self.loc.fid, self.loc))
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
    fn into_diag(self) -> Diagnostic {
        Diagnostic::error()
            .with_code(ErrorCode::InvalidDigitNumber)
            .with_message(format!("invalid digit in integer literal: {}", self.c))
            .with_label(Label::primary(self.loc_c.fid, self.loc_c))
            .with_label(
                Label::secondary(self.loc_i.fid, self.loc_i).with_message("in this integer"),
            )
    }
}

#[derive(Debug, Clone)]
pub struct TooLargeIntegerLiteral {
    /// location of the too large integer to fit in 128 bits
    pub loc: Span,
}

impl ToDiagnostic for TooLargeIntegerLiteral {
    fn into_diag(self) -> Diagnostic {
        Diagnostic::error()
            .with_code(ErrorCode::TooLargeIntegerLiteral)
            .with_message("integer literal is too large")
            .with_label(Label::primary(self.loc.fid, self.loc))
            .with_note(format!("integer exceeds the limit of `{}`", u128::MAX))
    }
}

#[derive(Debug, Clone)]
pub struct UnterminatedStringLiteral {
    /// location of the unterminated string literal
    pub loc: Span,
}

impl ToDiagnostic for UnterminatedStringLiteral {
    fn into_diag(self) -> Diagnostic {
        Diagnostic::error()
            .with_code(ErrorCode::UnterminatedStringLiteral)
            .with_message("unterminated string literal")
            .with_label(Label::primary(self.loc.fid, self.loc))
    }
}

// TODO: add location of the string literal or the char literal the error is in.
#[derive(Debug, Clone)]
pub struct UnknownCharacterEscape {
    pub es: char,
    pub loc: Span,
}

impl ToDiagnostic for UnknownCharacterEscape {
    fn into_diag(self) -> Diagnostic {
        Diagnostic::error()
            .with_code(ErrorCode::UnknownCharacterEscape)
            .with_message(format!("unknown character escape: {}", self.es))
            .with_label(Label::primary(self.loc.fid, self.loc))
    }
}

#[derive(Debug, Clone)]
pub struct ExpectedExponentPart {
    pub found: char,
    pub loc_c: Span,
    pub loc_float: Span,
}

impl ToDiagnostic for ExpectedExponentPart {
    fn into_diag(self) -> Diagnostic {
        Diagnostic::error()
            .with_code(ErrorCode::ExpectedExponentPart)
            .with_message(format!(
                "expected exponent part of hexadecimal floating point literal, but found {:?}",
                self.found
            ))
            .with_label(Label::primary(self.loc_c.fid, self.loc_c))
            .with_label(Label::secondary(self.loc_float.fid, self.loc_float))
    }
}

#[derive(Debug, Clone)]
pub struct NoDigitsInANonDecimal {
    pub loc: Span,
}

impl ToDiagnostic for NoDigitsInANonDecimal {
    fn into_diag(self) -> Diagnostic {
        Diagnostic::error()
            .with_code(ErrorCode::NoDigitsInANonDecimal)
            .with_message("no digits found after the base")
            .with_label(Label::primary(self.loc.fid, self.loc))
    }
}

#[derive(Debug, Clone)]
pub struct TooManyCodepointsInCharLiteral {
    pub loc: Span,
}

impl ToDiagnostic for TooManyCodepointsInCharLiteral {
    fn into_diag(self) -> Diagnostic {
        Diagnostic::error()
            .with_code(ErrorCode::TooManyCodepointsInCharLiteral)
            .with_message(
                "too many characters in character literal, can only contain one codepoint",
            )
            .with_note("if you want to write a string literal use double quotes: \"")
            .with_label(Label::primary(self.loc.fid, self.loc))
    }
}

#[derive(Debug, Clone)]
pub struct EmptyCharLiteral {
    pub loc: Span,
}

impl ToDiagnostic for EmptyCharLiteral {
    fn into_diag(self) -> Diagnostic {
        Diagnostic::error()
            .with_code(ErrorCode::EmptyCharLiteral)
            .with_message("empty character literal")
            .with_label(
                Label::primary(self.loc.fid, self.loc)
                    .with_message("expected one codepoint found zero"),
            )
    }
}

#[derive(Debug, Clone)]
pub struct NotEnoughHexDigits {
    pub loc: Span,
}

impl ToDiagnostic for NotEnoughHexDigits {
    fn into_diag(self) -> Diagnostic {
        Diagnostic::error()
            .with_code(ErrorCode::NotEnoughHexDigits)
            .with_message("not enough hexadecimal digits in escape sequence")
            .with_label(Label::primary(self.loc.fid, self.loc))
    }
}

#[derive(Debug, Clone)]
pub enum InvalidUnicodeNote {
    ExpectedOpeningBrace,
    EmptyUnicode,
    TooBig,
    ExpectedClosingBrace,
    MustNotBeASurrogate,
}

impl InvalidUnicodeNote {
    pub fn note_str(&self) -> &str {
        match self {
            Self::ExpectedOpeningBrace => "expected '{' after '\\u'",
            Self::EmptyUnicode => "this escape must have at least one hex digit",
            Self::TooBig => "this hex number doesn't fit in 32 bits",
            Self::ExpectedClosingBrace => "expected '}' at the end of the unicode escape",
            Self::MustNotBeASurrogate => "unicode escape must not be a surrogate",
        }
    }
}

#[derive(Debug, Clone)]
pub struct InvalidUnicodeEscape {
    pub note: InvalidUnicodeNote,
    pub loc: Span,
}

impl ToDiagnostic for InvalidUnicodeEscape {
    fn into_diag(self) -> Diagnostic {
        Diagnostic::error()
            .with_code(ErrorCode::InvalidUnicodeEscape)
            .with_message("invalid unicode escape")
            .with_label(Label::primary(self.loc.fid, self.loc).with_message(self.note.note_str()))
    }
}
