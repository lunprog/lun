//! This crate contains everything SIR related:
//! - the implementation of the SIR, in the [`sir`] module.
//! - the pretty-printing of the SIR, in the [`pretty`] module.
//!
//! [`sir`]: crate::sir
//! [`pretty`]: crate::pretty
//! [DSIR]: lunc_desugar
#![doc(
    html_logo_url = "https://raw.githubusercontent.com/lunprog/lun/main/src/assets/logo_no_bg_black.png"
)]

pub mod pretty;
pub mod sir;
