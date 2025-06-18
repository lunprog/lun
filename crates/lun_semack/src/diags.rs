//! Diagnostics that maybe emitted by the Semantic Checker.

use lun_diag::{ErrorCode, Label, ToDiagnostic, WarnCode};

use super::*;

#[derive(Debug, Clone)]
pub struct MismatchedTypes {
    pub expected: AtomicType,
    pub found: AtomicType,
    /// location of something that was written and tells why we expect this
    /// type, but MUST be an expr-type written, not just an expression.
    ///
    /// eg:
    ///
    /// ```lun
    /// var a: u64 = true;
    /// //     ^^^ in this case this would be the `due_to` of the mismatched
    /// //         types diagnostic
    /// ```
    pub due_to: Option<Span>,
    pub loc: Span,
}

impl ToDiagnostic for MismatchedTypes {
    fn into_diag(self) -> Diagnostic {
        Diagnostic::error()
            .with_code(ErrorCode::MismatchedTypes)
            .with_message("mismatched types")
            .with_label(Label::primary((), self.loc).with_message(format!(
                "expected `{}`, found `{}`",
                self.expected, self.found
            )))
            .with_labels_iter(
                self.due_to
                    .map(|loc| Label::secondary((), loc).with_message("expected due to this")),
            )
        // TODO: maybe change the message of this error to `mismatched types`
        // and put the `expected type {} found type {}` on the primary label
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
pub struct NeverUsedSymbol {
    pub kind: SymKind,
    pub name: String,
    pub loc: Span,
}

impl ToDiagnostic for NeverUsedSymbol {
    fn into_diag(self) -> Diagnostic<()> {
        Diagnostic::warning()
            .with_code(WarnCode::NeverUsedSymbol)
            .with_message(format!("{} `{}` is never used", self.kind, self.name))
            .with_label(Label::primary((), self.loc))
    }
}

#[derive(Debug, Clone)]
pub struct UnderscoreReservedIdent {
    pub loc: Span,
}

impl ToDiagnostic for UnderscoreReservedIdent {
    fn into_diag(self) -> Diagnostic<()> {
        Diagnostic::error()
            .with_code(ErrorCode::UnderscoreReservedIdentifier)
            .with_message("`_` is a reserved identifier")
            .with_note("you can't use `_` as a symbol name")
            .with_label(Label::primary((), self.loc))
    }
}

#[derive(Debug, Clone)]
pub struct UnderscoreInExpression {
    pub loc: Span,
}

impl ToDiagnostic for UnderscoreInExpression {
    fn into_diag(self) -> Diagnostic<()> {
        Diagnostic::error()
            .with_code(ErrorCode::UnderscoreInExpression)
            .with_message(
                "`_` can only be used in left hand side of assignement not in expressions",
            )
            .with_label(Label::primary((), self.loc))
    }
}
