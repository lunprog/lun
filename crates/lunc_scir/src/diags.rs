//! Diagnostics that can be emitted by the semantic checker.

use std::fmt::Display;

use lunc_diag::{ErrorCode, Label, ToDiagnostic, WarnCode};
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
    pub notes: Vec<String>,
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
            .with_notes(self.notes)
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
                "this function takes {} arguments but {} were provided",
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

#[derive(Debug, Clone)]
pub struct CallRequiresFuncType {
    pub found: Type,
    pub loc: Span,
}

impl ToDiagnostic for CallRequiresFuncType {
    fn into_diag(self) -> Diagnostic {
        Diagnostic::error()
            .with_code(ErrorCode::CallRequiresFuncType)
            .with_message("function call requires function type")
            .with_label(
                Label::primary(self.loc.fid, self.loc)
                    .with_message(format!("instead found '{}'", self.found)),
            )
    }
}

#[derive(Debug, Clone)]
pub struct UseOfUndefinedLabel {
    pub name: String,
    pub loc: Span,
}

impl ToDiagnostic for UseOfUndefinedLabel {
    fn into_diag(self) -> Diagnostic {
        Diagnostic::error()
            .with_code(ErrorCode::UseOfUndefinedLabel)
            .with_message(format!("use of undeclared label '{}'", self.name))
            .with_label(Label::primary(self.loc.fid, self.loc))
    }
}

#[derive(Debug, Clone)]
pub struct LabelKwOutsideLoopOrBlock<'a> {
    pub kw: &'a str,
    pub loc: Span,
}

impl<'a> ToDiagnostic for LabelKwOutsideLoopOrBlock<'a> {
    fn into_diag(self) -> Diagnostic {
        Diagnostic::error()
            .with_code(ErrorCode::LabelKwOutsideLoopOrBlock)
            .with_message(format!(
                "`{}` outside of a loop or a labeled block",
                self.kw,
            ))
            .with_label(Label::primary(self.loc.fid, self.loc))
    }
}

#[derive(Debug, Clone)]
pub struct BreakUseAnImplicitLabelInBlock {
    pub loc: Span,
}

impl ToDiagnostic for BreakUseAnImplicitLabelInBlock {
    fn into_diag(self) -> Diagnostic {
        Diagnostic::error()
            .with_code(ErrorCode::BreakUseAnImplicitLabelInBlock)
            .with_message("implicit label `break` inside of a labeled block")
            .with_label(Label::primary(self.loc.fid, self.loc).with_message(
                "'break' statement referring to a labeled block need to have a label",
            ))
    }
}

#[derive(Debug, Clone)]
pub struct CantContinueABlock {
    pub loc: Span,
}

impl ToDiagnostic for CantContinueABlock {
    fn into_diag(self) -> Diagnostic {
        Diagnostic::error()
            .with_code(ErrorCode::CantContinueABlock)
            .with_message("a block cannot be 'continue'd")
            .with_label(Label::primary(self.loc.fid, self.loc))
            .with_note("you might want to use a loop instead like 'while', 'for' or 'loop'.")
    }
}

#[derive(Debug, Clone)]
pub struct BreakFromLoopWithValue {
    pub loc: Span,
}

impl ToDiagnostic for BreakFromLoopWithValue {
    fn into_diag(self) -> Diagnostic {
        Diagnostic::error()
            .with_code(ErrorCode::BreakFromLoopWithValue)
            .with_message("'break' from a loop with a value")
            .with_label(
                Label::primary(self.loc.fid, self.loc)
                    .with_message("can only 'break' with a value from a labeled block"),
            )
    }
}

#[derive(Debug, Clone)]
pub struct WUnreachableCode {
    /// location of the statement that does not return
    pub noret_loc: Span,
    /// location of the following statement or expression that is unreachable
    pub loc: Span,
}

impl ToDiagnostic for WUnreachableCode {
    fn into_diag(self) -> Diagnostic {
        Diagnostic::warning()
            .with_code(WarnCode::UnreachableCode)
            .with_message("unreachable code")
            .with_label(Label::primary(self.loc.fid, self.loc).with_message("the unreachable code"))
            .with_label(
                Label::secondary(self.noret_loc.fid, self.noret_loc)
                    .with_message("any code following this statement is unreachable"),
            )
    }
}

#[derive(Debug, Clone)]
pub struct WUnusedLabel {
    /// location of the unused NAMED label
    pub loc: Span,
    /// name of the label
    pub label: String,
}

impl ToDiagnostic for WUnusedLabel {
    fn into_diag(self) -> Diagnostic {
        Diagnostic::warning()
            .with_code(WarnCode::UnusedLabel)
            .with_message(format!("unused label '{}'", self.label))
            .with_label(Label::primary(self.loc.fid, self.loc))
    }
}
