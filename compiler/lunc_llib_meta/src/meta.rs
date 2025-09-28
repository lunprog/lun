//! `.lmeta` file contained inside of a `.llib` static library file.

use chrono::{Local, NaiveDateTime};
use lunc_utils::target;
use serde::{Deserialize, Serialize};

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Lmeta {
    magic: [u8; 5],
    version: String,
    target: target::Triple,
    build_date: NaiveDateTime,
    // module: ModuleTree,
}

impl Lmeta {
    pub const MAGIC: [u8; 5] = *b"lmeta";

    /// Create a new Lmeta.
    pub fn new(version: String, target: target::Triple) -> Lmeta {
        let now = Local::now();

        Lmeta {
            magic: Lmeta::MAGIC,
            version,
            target,
            build_date: now.naive_local(),
        }
    }
}
