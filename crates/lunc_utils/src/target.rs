//! Targets

use std::{
    fmt::{self, Display},
    str::FromStr,
};

use serde::{
    Deserialize, Serialize,
    de::{self, Visitor},
};
use thiserror::Error;

/// Target format: <arch><[sub]>-<sys>-<env> where:
/// - arch = `x64_64`, `x86`, `arm`, `aarch64`, `riscv64`, `riscv32`
/// - sub  = for eg, riscv64 = `imaf`, `g`, `gc`
/// - sys  = `linux`, `windows`, `android`, `macos`, `none`
/// - env  = `gnu`, `msvc`, `elf`, `macho`
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct TargetTriplet {
    arch: Arch,
    sys: Sys,
    env: Env,
}

const _: () = {
    assert!(
        TargetTriplet::maybe_host_triplet().is_some(),
        "cannot compile to host target"
    );
};

impl TargetTriplet {
    /// List of all supported targets of the compiler
    pub const SUPPORTED_TARGETS: &[TargetTriplet] = &[TargetTriplet {
        arch: Arch::x86_64,
        sys: Sys::Linux,
        env: Env::Gnu,
    }];

    /// Returns the target triplet
    pub const fn maybe_host_triplet() -> Option<TargetTriplet> {
        let arch = if cfg!(target_arch = "x86_64") {
            Arch::x86_64
        } else if cfg!(target_arch = "x86") {
            Arch::x86
        } else if cfg!(target_arch = "arm") {
            Arch::arm
        } else if cfg!(target_arch = "aarch64") {
            Arch::aarch64
        } else if cfg!(target_arch = "riscv64") {
            Arch::riscv64
        } else if cfg!(target_arch = "riscv32") {
            Arch::riscv32
        } else {
            return None;
        };

        let sys = if cfg!(target_os = "linux") {
            Sys::Linux
        } else if cfg!(target_os = "windows") {
            Sys::Windows
        } else if cfg!(target_os = "android") {
            Sys::Android
        } else if cfg!(target_os = "macos") {
            Sys::Macos
        } else if cfg!(target_os = "none") {
            Sys::None
        } else {
            return None;
        };

        let env = if cfg!(target_env = "gnu") {
            Env::Gnu
        } else if cfg!(target_env = "msvc") {
            Env::Msvc
        } else if cfg!(target_env = "") && matches!(sys, Sys::Linux | Sys::None) {
            Env::Elf
        } else if cfg!(target_env = "")
            && let Sys::Macos = sys
        {
            Env::Macho
        } else {
            return None;
        };

        Some(TargetTriplet { arch, sys, env })
    }

    pub const fn host_target() -> TargetTriplet {
        TargetTriplet::maybe_host_triplet().unwrap()
    }
}

impl FromStr for TargetTriplet {
    type Err = TargetParsingError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let mut splits = s.split('-');

        let unknown_target = || UnknownTarget {
            target: s.to_string(),
        };

        let arch_s = splits.next().ok_or_else(unknown_target)?;
        let sys_s = splits.next().ok_or_else(unknown_target)?;
        let env_s = splits.next().ok_or_else(unknown_target)?;

        if splits.next().is_some() {
            return Err(unknown_target());
        }

        let arch = match arch_s {
            "x86_64" => Arch::x86_64,
            "x86" => Arch::x86,
            "arm" => Arch::arm,
            "aarch64" => Arch::aarch64,
            _ if arch_s.starts_with("riscv64") => Arch::riscv64,
            _ if arch_s.starts_with("riscv32") => Arch::riscv32,
            _ => {
                return Err(UnknownArch {
                    arch: arch_s.to_string(),
                    target: s.to_string(),
                });
            }
        };

        if arch == Arch::riscv32 || arch == Arch::riscv64 {
            todo!("implement parsing of risc-v's extensions")
        }

        let sys = match sys_s {
            "linux" => Sys::Linux,
            "windows" => Sys::Windows,
            "android" => Sys::Android,
            "macos" => Sys::Macos,
            "none" => Sys::None,
            _ => {
                return Err(UnknownSys {
                    sys: sys_s.to_string(),
                    target: s.to_string(),
                });
            }
        };

        let env = match env_s {
            "gnu" => Env::Gnu,
            "msvc" => Env::Msvc,
            "elf" => Env::Elf,
            "macho" => Env::Macho,
            _ => {
                return Err(UnknownEnv {
                    env: env_s.to_string(),
                    target: s.to_string(),
                });
            }
        };

        Ok(TargetTriplet { arch, sys, env })
    }
}

impl Serialize for TargetTriplet {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        serializer.serialize_str(&self.to_string())
    }
}

impl<'de> Deserialize<'de> for TargetTriplet {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        deserializer.deserialize_str(TargetTripletVisitor)
    }
}

pub struct TargetTripletVisitor;

impl<'de> Visitor<'de> for TargetTripletVisitor {
    type Value = TargetTriplet;

    fn expecting(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        write!(fmt, "a target")
    }

    fn visit_str<E>(self, v: &str) -> Result<Self::Value, E>
    where
        E: serde::de::Error,
    {
        TargetTriplet::from_str(v).map_err(de::Error::custom)
    }

    fn visit_string<E>(self, v: String) -> Result<Self::Value, E>
    where
        E: de::Error,
    {
        self.visit_str(&v)
    }
}

impl Display for TargetTriplet {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}-{}-{}", self.arch, self.sys, self.env)
    }
}

use TargetParsingError::*;

#[derive(Debug, Clone, Error)]
pub enum TargetParsingError {
    /// The target is unknown, use more specific error if possible like,
    /// UnknownArch
    #[error("unknown target: `{target}`, type `lunc -target help` for details")]
    UnknownTarget { target: String },
    /// The architecture in the target triple is unknown
    #[error(
        "unknown architecture `{arch}` in target `{target}`, type `lunc -target help` for details"
    )]
    UnknownArch { arch: String, target: String },
    /// The system in the target triple is unknown
    #[error("unknown system `{sys}` in target `{target}`, type `lunc -target help` for details")]
    UnknownSys { sys: String, target: String },
    /// The environment in the target triple is unknown
    #[error(
        "unknown environment `{env}` in target `{target}`, type `lunc -target help` for details"
    )]
    UnknownEnv { env: String, target: String },
}

/// Architecture with sub architecture
#[allow(non_camel_case_types)]
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Arch {
    x86_64,
    x86,
    arm,
    aarch64,
    riscv32,
    riscv64,
}

impl Display for Arch {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{}",
            match self {
                Arch::x86_64 => "x86_64",
                Arch::x86 => "x86",
                Arch::arm => "arm",
                Arch::aarch64 => "aarch64",
                Arch::riscv32 => "riscv32",
                Arch::riscv64 => "riscv64",
            }
        )
    }
}

/// System
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Sys {
    Linux,
    Windows,
    Macos,
    Android,
    None,
}

impl Display for Sys {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{}",
            match self {
                Sys::Linux => "linux",
                Sys::Windows => "windows",
                Sys::Macos => "macos",
                Sys::Android => "android",
                Sys::None => "none",
            }
        )
    }
}

/// Environment
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Env {
    Gnu,
    Msvc,
    // TODO: are those `elf` and `macho` environment appropriate? `none` could
    // replace them both
    Elf,
    Macho,
}

impl Display for Env {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{}",
            match self {
                Env::Gnu => "gnu",
                Env::Msvc => "msvc",
                Env::Elf => "elf",
                Env::Macho => "macho",
            }
        )
    }
}
