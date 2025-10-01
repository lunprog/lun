//! `.lmeta` file contained inside of a `.llib` static library file.

use std::{collections::HashMap, num::NonZeroUsize};

use chrono::{Local, NaiveDateTime};
use lunc_utils::{
    idtype::Database,
    symbol::{InternalSymbol, LazySymbol, Symbol},
    target,
};
use serde::{Deserialize, Serialize};
use thiserror::Error;

use crate::ModuleTree;

/// Error when dealing with Lmeta.
#[derive(Debug, Clone, Error)]
pub enum Error {
    #[error(transparent)]
    Postcard(#[from] postcard::Error),
    #[error(transparent)]
    Ron(#[from] ron::Error),
    #[error("symbol not referenced in the database of the meta file, id = {0}.")]
    UnreferencedSymbol(NonZeroUsize),
    #[error("bad magic, expected {magic:?} found {0:?}", magic = Lmeta::MAGIC)]
    BadMagic([u8; 5]),
}

/// Metadata contained inside of a TAR archive along side the object files of a
/// `llib` type of orb, compiled by the lunc compiler.
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
            build_date: now.naive_utc(),
            orbtree,
            sym_db: Symbol::database().lock().clone(),
        }
    }

    /// Serializes the Lmeta to a string of Ron.
    pub fn to_bytes(&self) -> Result<Vec<u8>, Error> {
        postcard::to_stdvec(self).map_err(Error::from)
    }

    /// Serializes the Lmeta to a pretty Ron string
    pub fn to_text(&self) -> Result<String, Error> {
        ron::ser::to_string_pretty(self, ron::ser::PrettyConfig::default()).map_err(Error::from)
    }

    /// Deserializes the bytes to a Lmeta.
    ///
    /// # Note
    ///
    /// This function doesn't convert the old symbol's id in the orbtree
    /// to new symbol's id. So a Lmeta, from this function **should not be
    /// used**, before their symbol id's getting converted to new ones, see
    /// [Lmeta::load_from_bytes].
    pub unsafe fn from_bytes(bytes: &[u8]) -> Result<Self, Error> {
        postcard::from_bytes(bytes).map_err(Error::from)
    }

    /// Deserializes the bytes to a Lmeta and perform the translation of the symbols.
    ///
    /// Also removes the database, because it is no longer needed.
    pub fn load_from_bytes(bytes: &[u8]) -> Result<Self, Error> {
        // SAFETY: we will convert old to new ids just after that.
        let mut lmeta = unsafe { Self::from_bytes(bytes)? };

        if lmeta.magic != Self::MAGIC {
            return Err(Error::BadMagic(lmeta.magic));
        }

        // lmeta symbol -> actual symbol
        let mut old_to_new_symbol: HashMap<NonZeroUsize, Symbol> = HashMap::new();

        for (lsym, value) in lmeta.sym_db.data() {
            old_to_new_symbol.insert(
                lsym,
                Symbol::with_internal(value.value.read().unwrap().clone()),
            );
        }

        struct ModMapper {
            // lmeta symbol -> actual symbol
            old_to_new: HashMap<NonZeroUsize, Symbol>,
        }

        impl ModMapper {
            fn map_sym(&self, s: Symbol) -> Result<Symbol, Error> {
                Ok(self
                    .old_to_new
                    .get(&s.id())
                    .ok_or_else(|| Error::UnreferencedSymbol(s.id()))?
                    .clone())
            }

            fn map_modtree(&self, old_tree: ModuleTree) -> Result<ModuleTree, Error> {
                let mut new_tree = ModuleTree {
                    submodules: HashMap::new(),
                    defs: HashMap::new(),
                    root_name: old_tree.root_name,
                    sym: match old_tree.sym {
                        LazySymbol::Name(n) => LazySymbol::Name(n),
                        LazySymbol::Sym(s) => LazySymbol::Sym(self.map_sym(s)?),
                    },
                };

                for (defname, defsym) in old_tree.defs {
                    new_tree.defs.insert(defname, self.map_sym(defsym)?);
                }

                for (modname, modtree) in old_tree.submodules {
                    new_tree
                        .submodules
                        .insert(modname, self.map_modtree(modtree)?);
                }

                Ok(new_tree)
            }
        }

        let mapper = ModMapper {
            old_to_new: old_to_new_symbol,
        };

        lmeta.orbtree = mapper.map_modtree(lmeta.orbtree)?;

        // create new dummy database
        lmeta.sym_db = Database::new();

        Ok(lmeta)
    }

    pub fn eq_ignore_db(&self, other: &Self) -> bool {
        self.magic == other.magic
            && self.version == other.version
            && self.target == other.target
            && self.build_date == other.build_date
            && self.orbtree == other.orbtree
    }
}

#[cfg(test)]
mod tests {
    use std::error::Error as StdError;

    use lunc_utils::{idtype, target::triple};

    use super::*;

    type TestRes = Result<(), Box<dyn StdError>>;

    #[test]
    fn lmeta_vice_versa_empty() -> TestRes {
        let _lock = idtype::TEST_LOCK.lock()?;

        let empty = "empty".to_string();
        let vice = Lmeta::new(
            "0.1.0".to_string(),
            triple!("x86_64-unknown-linux-gnu"),
            ModuleTree::new(Some(empty.clone()), LazySymbol::Name(empty)),
        );

        let bytes = vice.to_bytes().unwrap();
        let versa = Lmeta::load_from_bytes(&bytes).unwrap();

        assert!(vice.eq_ignore_db(&versa));

        Ok(())
    }
}
