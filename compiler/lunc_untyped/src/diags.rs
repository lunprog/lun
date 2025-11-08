//! Diagnostics of the UTIR stage

use lunc_diag::{Diagnostic, ErrorCode, Label, ToDiagnostic};
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
