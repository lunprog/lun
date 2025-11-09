//! Diagnostics of the UTIR stage

use lunc_diag::{Diagnostic, ErrorCode, Label, ToDiagnostic};
use lunc_token::LitKind;
use lunc_utils::Span;

#[derive(Debug, Clone)]
pub struct FunctionInGlobalMut {
    /// either 'function definition' or 'function declaration'
    pub fun: &'static str,
    /// loc of the global def
    pub loc: Span,
}

impl FunctionInGlobalMut {
    pub const FUNDEF: &str = "function definition";
    pub const FUNDECL: &str = "function declaration";
}

impl ToDiagnostic for FunctionInGlobalMut {
    fn into_diag(self) -> Diagnostic {
        Diagnostic::error()
            .with_code(ErrorCode::FunctionInGlobalMut)
            .with_message(format!(
                "cannot define a {} inside of a mutable global definition",
                self.fun
            ))
            .with_label(Label::primary(self.loc.fid, self.loc))
    }
}

#[derive(Debug, Clone)]
pub struct UnknownLitTag {
    pub kind: LitKind,
    pub tag: String,
    pub loc: Span,
}

impl UnknownLitTag {
    fn note(&self) -> Option<&'static str> {
        match self.kind {
            LitKind::Char => Some("currently character literals do not support tags."),
            LitKind::Integer => Some("valid tags are integer types like, 'u8', 'u16', 'isz' etc."),
            LitKind::Float => Some("valid float tags are float types: 'f32', 'f64'."),
            LitKind::Str => Some("valid string literal tag is 'c'."),
            LitKind::CStr => None,
        }
    }
}

impl ToDiagnostic for UnknownLitTag {
    fn into_diag(self) -> Diagnostic {
        Diagnostic::error()
            .with_code(ErrorCode::UnknownLitTag)
            .with_message(format!(
                "unknown literal tag '{}' for {}",
                self.tag, self.kind
            ))
            .with_notes_iter(self.note().map(|s| s.to_string()))
            .with_label(Label::primary(self.loc.fid, self.loc))
    }
}
