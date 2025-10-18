//! Diagnostics that may be emitted by the parser.

use lunc_diag::{Diagnostic, ErrorCode, Label, ToDiagnostic};
use lunc_token::{ExpTokenSet, Token, TokenType};
use lunc_utils::{DEFAULT_MAX_LEVENSHTEIN_DISTANCE, Span, list_fmt, suggest};

use crate::directive::Directive;

#[derive(Debug, Clone)]
pub struct ExpectedToken {
    /// what token was expected?
    expected: Vec<String>,
    /// what was found instead of the expected token
    found: TokenType,
    /// semicolon info.
    semi_loc: Option<Span>,
    /// location of the found token
    loc: Span,
}

impl ExpectedToken {
    /// Empty expected token, used when the expected are added later.
    pub const EMPTY: [String; 0] = [];

    /// Create a new ExpectedToken diag.
    pub fn new<I: IntoIterator<Item = S>, S: ToString>(expected: I, found: Token) -> ExpectedToken {
        ExpectedToken {
            expected: expected.into_iter().map(|s| s.to_string()).collect(),
            found: found.tt,
            semi_loc: None,
            loc: found.loc,
        }
    }

    pub fn add_expects(mut self, expects: ExpTokenSet) -> Self {
        self.expected
            .extend(expects.iter().map(|tr| tr.to_string()));
        self
    }

    pub fn add_semi(&mut self, semi_loc: Span) {
        self.semi_loc = Some(semi_loc);
    }

    fn fmt_msg(&self) -> String {
        let len = self.expected.len();
        assert_ne!(len, 0);

        let expected = list_fmt(&self.expected);

        format!("expected {}, found {}", expected, self.found)
    }
}

impl ToDiagnostic for ExpectedToken {
    fn into_diag(self) -> Diagnostic {
        Diagnostic::error()
            .with_code(ErrorCode::ExpectedToken)
            .with_message(self.fmt_msg())
            .with_label({
                let mut label = Label::primary(self.loc.fid, self.loc);

                if self.semi_loc.is_some() {
                    label.message = format!("unexpected {}", self.found);
                }

                label
            })
            .with_labels_iter(self.semi_loc.map(|loc| {
                Label::secondary(loc.fid, loc).with_message("help: add `;` after this token")
            }))
    }
}

#[derive(Debug, Clone)]
pub struct UnknownDirective {
    pub name: String,
    pub loc: Span,
}

impl ToDiagnostic for UnknownDirective {
    fn into_diag(self) -> Diagnostic {
        let suggestion = suggest(
            &self.name,
            Directive::DIRECTIVES,
            DEFAULT_MAX_LEVENSHTEIN_DISTANCE,
        );

        Diagnostic::error()
            .with_code(ErrorCode::UnknownDirective)
            .with_message(format!("unknown directive '{}'", self.name))
            .with_label(Label::primary(self.loc.fid, self.loc))
            .with_notes_iter(suggestion.map(|suggested| format!("did you mean '{suggested}'?")))
    }
}

#[derive(Debug, Clone)]
pub struct UnknownAbi {
    /// the unknown abi
    pub abi: String,
    /// the loc of the string literal
    pub loc: Span,
}

impl ToDiagnostic for UnknownAbi {
    fn into_diag(self) -> Diagnostic {
        Diagnostic::error()
            .with_code(ErrorCode::UnknownAbi)
            .with_message(format!("ABI '{}' isn't known", self.abi))
            .with_label(Label::primary(self.loc.fid, self.loc))
    }
}
