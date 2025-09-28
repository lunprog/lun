//! `.lmeta` file contained inside of a `.llib` static library file.

use chrono::{Local, NaiveDateTime};
use lunc_utils::{
    idtype::Database,
    symbol::{InternalSymbol, Symbol},
    target,
};
use serde::{Deserialize, Serialize};

use crate::ModuleTree;

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Lmeta {
    magic: [u8; 5],
    version: String,
    target: target::Triple,
    build_date: NaiveDateTime,
    orbtree: ModuleTree,
    sym_db: Database<InternalSymbol>,
}

impl Lmeta {
    pub const MAGIC: [u8; 5] = *b"lmeta";

    /// Create a new Lmeta.
    pub fn new(version: String, target: target::Triple, orbtree: ModuleTree) -> Lmeta {
        let now = Local::now();

        Lmeta {
            magic: Lmeta::MAGIC,
            version,
            target,
            build_date: now.naive_local(),
            orbtree,
            sym_db: Symbol::database().lock().clone(),
        }
    }

    /// Serializes the Lmeta to a string of Ron.
    pub fn to_bytes(&self) -> Result<Vec<u8>, postcard::Error> {
        postcard::to_stdvec(self)
    }
}
