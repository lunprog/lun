//! Diagnostics of the UTIR stage

use lunc_diag::{Diagnostic, ErrorCode, Label, ToDiagnostic};
use lunc_token::LitKind;
use lunc_utils::Span;

pub const FUNDEF: &str = "function definition";
pub const FUNDECL: &str = "function declaration";
pub const GLOBAL_UNINIT: &str = "global uninit";
pub const GLOBAL_DEF: &str = "global definition";
pub const MODULE: &str = "module";
pub const EXTERN_BLOCK: &str = "extern block";
pub const DIRECTIVE: &str = "directive";

#[derive(Debug, Clone)]
pub struct FunctionInGlobalMut {
    /// either 'function definition' or 'function declaration'
    pub fun: &'static str,
    /// loc of the global def
    pub loc: Span,
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

#[derive(Debug, Clone)]
pub struct OutsideExternBlock {
    /// name of the item either `function declaration` or `global uninit`
    pub item_name: &'static str,
    /// location of the fundecl
    pub loc: Span,
}

impl ToDiagnostic for OutsideExternBlock {
    fn into_diag(self) -> Diagnostic {
        Diagnostic::error()
            .with_code(ErrorCode::OutsideExternBlock)
            .with_message(format!("{} must be inside of an extern block.", self.item_name))
            .with_label(Label::primary(self.loc.fid, self.loc))
            .with_note("consider moving the function declaration into an extern block like 'extern \"C\" { .. }'.")
    }
}

#[derive(Debug, Clone)]
pub struct ItemNotAllowedInExternBlock {
    /// name of the item
    pub item: &'static str,
    /// optional note
    pub note: Option<&'static str>,
    /// location of the item
    pub loc: Span,
    /// location of the external block
    pub extern_block_loc: Span,
}

impl ToDiagnostic for ItemNotAllowedInExternBlock {
    fn into_diag(self) -> Diagnostic {
        Diagnostic::error()
            .with_code(ErrorCode::ItemNotAllowedInExternBlock)
            .with_message(format!(
                "a {} isn't allowed inside of an extern block.",
                self.item
            ))
            .with_label(Label::primary(self.loc.fid, self.loc).with_message("defined here."))
            .with_label(
                Label::secondary(self.extern_block_loc.fid, self.extern_block_loc)
                    .with_message("inside this extern block"),
            )
            .with_notes_iter(self.note.map(|s| s.to_string()))
    }
}
