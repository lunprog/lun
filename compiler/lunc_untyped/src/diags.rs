//! Diagnostics of the UTIR stage

use std::sync::Arc;

use lunc_diag::{Diagnostic, ErrorCode, Label, ToDiagnostic};
use lunc_token::LitKind;
use lunc_utils::{Span, list_fmt};

// Items
pub const FUNDEF: &str = "function definition";
pub const FUNDECL: &str = "function declaration";
pub const GLOBAL_UNINIT: &str = "global uninit";
pub const GLOBAL_DEF: &str = "global definition";
pub const MODULE: &str = "module";
pub const EXTERN_BLOCK: &str = "extern block";
pub const DIRECTIVE: &str = "directive";

// Expressions
pub const BREAK: &str = "break";
pub const CONTINUE: &str = "continue";

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

#[derive(Debug, Clone)]
pub struct BreakWithValueUnsupported {
    pub loc: Span,
}

impl ToDiagnostic for BreakWithValueUnsupported {
    fn into_diag(self) -> Diagnostic {
        Diagnostic::error()
            .with_code(ErrorCode::BreakWithValueUnsupported)
            .with_message("'break' from a predicate or iterator loop with a value")
            .with_label(Label::primary(self.loc.fid, self.loc).with_message(
                "can only 'break' with a value from a labeled block or an infinite loop",
            ))
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
pub struct CantEvaluateAtComptime {
    /// optional note
    pub note: Option<String>,
    /// location of the entire expression trying to be evaluated at compile-time
    pub loc_expr: Span,
    /// location of the (maybe?) inner expression that fails to evaluate at comptime
    pub loc: Span,
}

impl ToDiagnostic for CantEvaluateAtComptime {
    fn into_diag(self) -> Diagnostic {
        Diagnostic::error()
            .with_code(ErrorCode::CantEvaluateAtComptime)
            .with_message("unable to evaluate expression at compile-time")
            .with_label(Label::primary(self.loc.fid, self.loc))
            .with_label(
                Label::secondary(self.loc_expr.fid, self.loc_expr)
                    .with_message("due to this expression"),
            )
            .with_notes_iter(self.note)
    }
}

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub struct MtComplex {
    pub due_to: Option<Span>,
    pub loc: Span,
    pub notes: Vec<String>,
}

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub enum PreMt {
    Simple(Span),
    Complex(Arc<MtComplex>),
}

impl PreMt {
    pub fn new(
        loc: Span,
        due_to: impl Into<Option<Span>>,
        notes: impl IntoIterator<Item = String>,
    ) -> PreMt {
        let due_to = due_to.into();
        let notes: Vec<_> = notes.into_iter().collect();

        if due_to.is_none() && notes.is_empty() {
            PreMt::Simple(loc)
        } else {
            PreMt::Complex(Arc::new(MtComplex { due_to, loc, notes }))
        }
    }
}

impl PreMt {
    pub fn loc(&self) -> Span {
        match self {
            PreMt::Simple(loc) => *loc,
            PreMt::Complex(complex) => complex.loc,
        }
    }

    pub fn due_to(&self) -> Option<Span> {
        match self {
            PreMt::Simple(_) => None,
            PreMt::Complex(complex) => complex.due_to,
        }
    }

    pub fn notes(&self) -> Vec<String> {
        match self {
            PreMt::Simple(_) => Vec::new(),
            PreMt::Complex(complex) => complex.notes.clone(),
        }
    }
}

impl From<Span> for PreMt {
    fn from(value: Span) -> Self {
        PreMt::Simple(value)
    }
}

#[derive(Debug, Clone)]
pub struct MismatchedTypes {
    pub expected: Vec<String>,
    pub found: String,
    /// location of something that was written and tells why we expect this
    /// type, but MUST be an expr-type written, not just an expression.
    ///
    /// eg:
    ///
    /// ```lun
    /// a :: fun() {
    ///     let a: u64 = true;
    ///     //     ^^^ in this case this would be the `due_to` of the mismatched
    ///     //         types diagnostic
    /// }
    /// ```
    pub due_to: Option<Span>,
    pub notes: Vec<String>,
    pub loc: Span,
}

impl MismatchedTypes {
    pub fn new(pre: PreMt, expected: Vec<String>, found: String) -> MismatchedTypes {
        MismatchedTypes {
            expected,
            found,
            due_to: pre.due_to(),
            notes: pre.notes(),
            loc: pre.loc(),
        }
    }
}

impl ToDiagnostic for MismatchedTypes {
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
