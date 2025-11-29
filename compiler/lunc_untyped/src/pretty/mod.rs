//! Pretty-printing of UTIR.
//!
//! There is two flavors, the tree like flavor [tree] and the [lun-like syntax][lun] one.

pub mod lun;
pub mod tree;

/// Tree flavor of the pretty-printing.
pub struct TreeFlavor;

/// Lun-flavor of pretty-printing.
pub struct LunFlavor;
