//! Diagnostics that may be emitted by the desugarrer.

use std::path::PathBuf;

use lunc_diag::{Diagnostic, ErrorCode, Label, ToDiagnostic};
use lunc_utils::Span;

#[derive(Debug, Clone)]
pub struct ModuleFileDoesnotExist {
    pub name: String,
    pub expected_path: PathBuf,
    pub loc: Span,
}

impl ToDiagnostic for ModuleFileDoesnotExist {
    fn into_diag(self) -> Diagnostic {
        Diagnostic::error()
            .with_code(ErrorCode::ModuleFileDoesnotExist)
            .with_message(format!("file not found for module '{}'", self.name))
            .with_label(Label::primary(self.loc.fid, self.loc))
            .with_note(format!(
                "help: to create the module '{}', create the file at path '{}'",
                self.name,
                self.expected_path.display()
            ))
    }
}
