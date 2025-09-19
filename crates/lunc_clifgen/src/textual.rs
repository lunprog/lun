//! Support for textual format of Clif

use std::fmt::Write;

use cranelift_codegen::ir::Function;
use lunc_utils::symbol;

/// Textual representation of clif.
#[derive(Debug)]
pub struct TextualClif {
    /// result
    pub(crate) res: String,
    /// is textual repr enabled?
    enabled: bool,
}

impl TextualClif {
    /// Create a new textual clif repr
    pub fn new(enabled: bool) -> TextualClif {
        TextualClif {
            res: String::new(),
            enabled,
        }
    }

    /// Write a fundef to the textual repr if enabled
    pub fn write_fundef(&mut self, fundef: &Function, sym: &symbol::Symbol) {
        if self.enabled {
            writeln!(
                self.res,
                "\n; name = {:?}, realname = {:?}",
                sym.name(),
                sym.realname().unwrap()
            )
            .unwrap();
            write!(self.res, "{}", fundef.display()).unwrap();
        }
    }
}
