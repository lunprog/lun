//! `.lmeta` file contained inside of a `.llib` static library file.
#![doc(
    html_logo_url = "https://raw.githubusercontent.com/lunprog/lun/main/src/assets/logo_no_bg_black.png"
)]

use std::num::NonZeroUsize;

use chrono::{Local, NaiveDateTime};
use lunc_utils::target;
use serde::{Deserialize, Serialize};
use thiserror::Error;

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
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct Lmeta {
    magic: [u8; 5],
    version: String,
    target: target::Triple,
    build_date: NaiveDateTime,
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
            build_date: now.naive_utc(),
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
    pub fn load_from_bytes(bytes: &[u8]) -> Result<Self, Error> {
        // SAFETY: we will convert old to new ids just after that.
        let lmeta: Lmeta = postcard::from_bytes(bytes).map_err(Error::from)?;

        if lmeta.magic != Self::MAGIC {
            return Err(Error::BadMagic(lmeta.magic));
        }

        Ok(lmeta)
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

        let vice = Lmeta::new("0.1.0".to_string(), triple!("x86_64-unknown-linux-gnu"));

        let bytes = vice.to_bytes().unwrap();
        let versa = Lmeta::load_from_bytes(&bytes).unwrap();

        assert_eq!(vice, versa);

        Ok(())
    }
}
