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

#[derive(Debug, Clone)]
pub struct NameDefinedMultipleTimes<'a> {
    pub name: &'a str,
    // location of the previous definition
    pub loc_previous: Span,
    // location of the new definition
    pub loc: Span,
}

impl<'a> ToDiagnostic for NameDefinedMultipleTimes<'a> {
    fn into_diag(self) -> Diagnostic {
        Diagnostic::error()
            .with_code(ErrorCode::NameDefinedMultipleTimes)
            .with_message(format!(
                "the name `{}` is defined multiple times",
                self.name
            ))
            .with_label(
                Label::primary(self.loc.fid, self.loc.clone())
                    .with_message(format!("defined `{}` a second time here", self.name)),
            )
            .with_label(
                Label::secondary(self.loc.fid, self.loc_previous)
                    .with_message("defined here for the first time"),
            )
    }
}

#[derive(Debug, Clone)]
pub struct UnderscoreReservedIdent {
    pub loc: Span,
}

impl ToDiagnostic for UnderscoreReservedIdent {
    fn into_diag(self) -> Diagnostic {
        Diagnostic::error()
            .with_code(ErrorCode::UnderscoreReservedIdentifier)
            .with_message("`_` is a reserved identifier")
            .with_note("you can't use `_` as a symbol name")
            .with_label(Label::primary(self.loc.fid, self.loc))
    }
}

#[derive(Debug, Clone)]
pub struct NotFoundInScope {
    pub name: String,
    pub loc: Span,
}

impl ToDiagnostic for NotFoundInScope {
    fn into_diag(self) -> Diagnostic {
        Diagnostic::error()
            .with_code(ErrorCode::NotFoundInScope)
            .with_message(format!("cannot find `{}` in this scope", self.name))
            .with_label(Label::primary(self.loc.fid, self.loc))
    }
}

#[derive(Debug, Clone)]
pub struct UnderscoreInExpression {
    pub loc: Span,
}

impl ToDiagnostic for UnderscoreInExpression {
    fn into_diag(self) -> Diagnostic {
        Diagnostic::error()
            .with_code(ErrorCode::UnderscoreInExpression)
            .with_message("`_` can only be used in left hand side of assignment not in expressions")
            .with_label(Label::primary(self.loc.fid, self.loc))
    }
}
