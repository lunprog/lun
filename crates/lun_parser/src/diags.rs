//! Diagnostics that may be emitted by the parser.

use lun_diag::{Diagnostic, ErrorCode, Label, ToDiagnostic};
use lun_utils::{
    Span,
    token::{Punctuation, TokenType},
};

use std::fmt::{Display, Write};

pub struct ExpectedToken {
    /// what token was expected?
    expected: Vec<Box<dyn Display>>,
    /// what was found instead of the expected token
    found: TokenType,
    /// where did the error occured, during the parsing of an expression, a
    /// statement? etc
    node: Option<String>,
    /// location of the found token
    loc: Span,
}

impl ExpectedToken {
    pub fn new<I, S, L>(expected: I, found: TokenType, node: Option<S>, loc: L) -> ExpectedToken
    where
        I: IntoDisplayables,
        S: ToString,
        L: Into<Span>,
    {
        ExpectedToken {
            expected: expected.into_displayables(),
            found,
            node: node.map(|s| s.to_string()),
            loc: loc.into(),
        }
    }

    fn fmt_msg(&self) -> String {
        let len = self.expected.len();
        assert_ne!(len, 0);

        let expected = if len == 1 {
            self.expected[0].to_string()
        } else {
            let mut res = String::new();

            for (idx, token) in self.expected.iter().enumerate() {
                if idx == self.expected.len() - 2 {
                    write!(res, "{token} ")
                } else if idx == self.expected.len() - 1 {
                    write!(res, "or {token}")
                } else {
                    write!(res, "{token}, ")
                }
                .unwrap();
            }

            res
        };

        let node = self
            .node
            .clone()
            .map(|s| format!(" for a {s}"))
            .unwrap_or_default();

        // TODO: change the msg to something like `unexpected integer while parsing expression, expected ...`
        format!("expected {}{}, found {}", expected, node, self.found)
    }
}

/// A trait to be able to accept both a simple value T and an array [T; N] of
/// values and turns it into a list.
///
/// Where T implements Display.
pub trait IntoDisplayables {
    fn into_displayables(self) -> Vec<Box<dyn Display>>;
}

impl IntoDisplayables for &'static str {
    fn into_displayables(self) -> Vec<Box<dyn Display>> {
        vec![Box::new(self)]
    }
}

impl IntoDisplayables for Punctuation {
    fn into_displayables(self) -> Vec<Box<dyn Display>> {
        vec![Box::new(self)]
    }
}

impl IntoDisplayables for TokenType {
    fn into_displayables(self) -> Vec<Box<dyn Display>> {
        vec![Box::new(self)]
    }
}

impl<T: Display + Clone + 'static, const N: usize> IntoDisplayables for [T; N] {
    fn into_displayables(self) -> Vec<Box<dyn Display>> {
        fn clone_to_boxed_display<T: Display + Clone + 'static>(val: &T) -> Box<dyn Display> {
            Box::new(val.clone())
        }
        self.iter().map(|d| clone_to_boxed_display(d)).collect()
    }
}

impl ToDiagnostic for ExpectedToken {
    fn into_diag(self) -> Diagnostic {
        Diagnostic::error()
            .with_code(ErrorCode::ExpectedToken)
            .with_message(self.fmt_msg())
            .with_label(Label::primary((), self.loc))
    }
}

#[derive(Debug, Clone)]
pub struct ReachedEOF {
    pub loc: Span,
}

impl ToDiagnostic for ReachedEOF {
    fn into_diag(self) -> Diagnostic<()> {
        Diagnostic::error()
            .with_code(ErrorCode::ReachedEOF)
            .with_message("reached end of file too early")
            .with_label(Label::primary((), self.loc))
    }
}
