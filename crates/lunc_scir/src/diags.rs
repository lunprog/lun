//! Diagnostics that can be emitted by the semantic checker.

use std::fmt::Display;

use lunc_diag::{ErrorCode, Label, ToDiagnostic};
use lunc_utils::{Span, list_fmt};

use super::*;

#[derive(Debug, Clone)]
pub struct MismatchedTypes<E: Display> {
    pub expected: Vec<E>,
    pub found: Type,
    /// location of something that was written and tells why we expect this
    /// type, but MUST be an expr-type written, not just an expression.
    ///
    /// eg:
    ///
    /// ```lun
    /// let a: u64 = true;
    /// //     ^^^ in this case this would be the `due_to` of the mismatched
    /// //         types diagnostic
    /// ```
    pub due_to: OSpan,
    pub note: Option<String>,
    pub loc: Span,
}

impl<E: Display> ToDiagnostic for MismatchedTypes<E> {
    fn into_diag(self) -> Diagnostic {
        Diagnostic::error()
            .with_code(ErrorCode::MismatchedTypes)
            .with_message("mismatched types")
            .with_label(Label::primary(self.loc.fid, self.loc).with_message(format!(
                "expected `{}`, found `{}`",
                list_fmt(&self.expected),
                self.found
            )))
            .with_labels_iter(
                self.due_to
                    .map(|loc| Label::secondary(loc.fid, loc).with_message("expected due to this")),
            )
            .with_notes_iter(self.note)
    }
}

#[derive(Debug, Clone)]
pub struct ExpectedTypeFoundExpr {
    pub loc: Span,
}

impl ToDiagnostic for ExpectedTypeFoundExpr {
    fn into_diag(self) -> Diagnostic {
        Diagnostic::error()
            .with_code(ErrorCode::ExpectedTypeFoundExpr)
            .with_message("expected type found an expression")
            .with_label(Label::primary(self.loc.fid, self.loc))
    }
}

#[derive(Debug, Clone)]
pub struct ExpectedPlaceExpression {
    pub loc: Span,
    pub lhs_assign: bool,
}

impl ToDiagnostic for ExpectedPlaceExpression {
    fn into_diag(self) -> Diagnostic {
        Diagnostic::error()
            .with_code(ErrorCode::ExpectedPlaceExpression)
            .with_message("expected this expression to be a place expression")
            .with_notes(if self.lhs_assign {
                vec!["the left-hand side of an assignment must be a place.".to_string()]
            } else {
                vec![]
            })
            .with_label(Label::primary(self.loc.fid, self.loc))
    }
}

#[derive(Debug, Clone)]
pub struct ArityDoesntMatch {
    /// expected amount of arguments
    pub expected: usize,
    /// how many arguments we got?
    pub got: usize,
    /// location of the callee
    pub loc: Span,
}

impl ToDiagnostic for ArityDoesntMatch {
    fn into_diag(self) -> Diagnostic {
        Diagnostic::error()
            .with_code(ErrorCode::ArityDoesntMatch)
            .with_message(format!(
                "this function takes {} arguments but only {} were provided",
                self.expected, self.got
            ))
            .with_label(Label::primary(self.loc.fid, self.loc))
    }
}

#[derive(Debug, Clone)]
pub struct CantResolveComptimeValue {
    /// location of the entire expression trying to be evaluated at compile-time
    pub loc_expr: Span,
    /// location of the (maybe?) inner expression that fails to evaluate at comptime
    pub loc: Span,
}

impl ToDiagnostic for CantResolveComptimeValue {
    fn into_diag(self) -> Diagnostic {
        Diagnostic::error()
            .with_code(ErrorCode::CantResolveComptimeValue)
            .with_message("unable to resolve expression at comptime")
            .with_label(Label::primary(self.loc.fid, self.loc))
            .with_label(
                Label::secondary(self.loc_expr.fid, self.loc_expr)
                    .with_message("due to this expression"),
            )
    }
}

#[derive(Debug, Clone)]
pub struct TypeAnnotationsNeeded {
    pub loc: Span,
}

impl ToDiagnostic for TypeAnnotationsNeeded {
    fn into_diag(self) -> Diagnostic {
        Diagnostic::error()
            .with_code(ErrorCode::TypeAnnotationsNeeded)
            .with_message("type annotations needed")
            .with_label(Label::primary(self.loc.fid, self.loc))
    }
}
