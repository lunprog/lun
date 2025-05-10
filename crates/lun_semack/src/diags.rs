//! Diagnostics that maybe emitted by the Semantic Checker.

use lun_diag::{ErrorCode, Label, ToDiagnostic};
use lun_utils::list_fmt;

use super::*;

#[derive(Debug, Clone)]
pub struct ExpectedType {
    pub expected: Vec<Type>,
    pub found: Type,
    pub loc: Span,
}

impl ToDiagnostic for ExpectedType {
    fn into_diag(self) -> Diagnostic {
        Diagnostic::error()
            .with_code(ErrorCode::ExpectedType)
            .with_message(format!(
                "expected type {} found type {}",
                list_fmt(&self.expected),
                self.found,
            ))
            .with_label(Label::primary((), self.loc))
    }
}

#[derive(Debug, Clone)]
pub struct ExpectedTypeFoundExpr {
    pub loc: Span,
}

impl ToDiagnostic for ExpectedTypeFoundExpr {
    fn into_diag(self) -> Diagnostic<()> {
        Diagnostic::error()
            .with_code(ErrorCode::ExpectedTypeFoundExpr)
            .with_message("expected type found an expression")
            .with_label(Label::primary((), self.loc))
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
            .with_label(Label::primary((), self.loc))
    }
}

#[derive(Debug, Clone)]
pub struct CallRequiresFuncType {
    pub is_expr: bool,
    pub loc: Span,
}

impl ToDiagnostic for CallRequiresFuncType {
    fn into_diag(self) -> Diagnostic {
        Diagnostic::error()
            .with_code(ErrorCode::CallRequiresFuncType)
            .with_message(if self.is_expr {
                "call expression requires function type"
            } else {
                "function call requires function type"
            })
            .with_label(Label::primary((), self.loc))
    }
}

#[derive(Debug, Clone)]
pub struct TypeAnnotationsNeeded {
    pub loc: Span,
}

impl ToDiagnostic for TypeAnnotationsNeeded {
    fn into_diag(self) -> Diagnostic {
        // TODO: add a secondary label to show the user where to put the type annotation
        Diagnostic::error()
            .with_code(ErrorCode::TypeAnnotationsNeeded)
            .with_message("type annotations needed")
            .with_label(Label::primary((), self.loc))
    }
}

#[derive(Debug, Clone)]
pub struct ReturnOutsideFunc {
    pub loc: Span,
}

impl ToDiagnostic for ReturnOutsideFunc {
    fn into_diag(self) -> Diagnostic<()> {
        Diagnostic::error()
            .with_code(ErrorCode::ReturnOutsideFunc)
            .with_message("used a return statement outside of a function body")
            .with_label(Label::primary((), self.loc))
    }
}
