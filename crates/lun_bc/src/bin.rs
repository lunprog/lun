//! The file type of Lun, `.lb`.

use std::{
    fmt::Display,
    io::{Read, Write},
};
use thiserror::Error;

use crate::{BcBlob, DataPool};

/// A type that can be build from and converted to bytes.
pub trait ByteRepr<const N: usize> {
    const SIZE: usize = N;

    fn from_bytes(bytes: [u8; N]) -> Self;

    #[track_caller]
    fn from_bytes_ref(bytes: &[u8]) -> Self
    where
        Self: Sized,
    {
        Self::from_bytes(bytes.try_into().unwrap())
    }

    fn as_bytes(&self) -> [u8; N];
}

macro_rules! impl_int_byte_repr {
    ($ty:ty) => {
        impl ByteRepr<{size_of::<$ty>()}> for $ty {
            #[track_caller]
            fn from_bytes(bytes: [u8; Self::SIZE]) -> Self {
                <$ty>::from_le_bytes(bytes.try_into().unwrap())
            }

            fn as_bytes(&self) -> [u8; Self::SIZE] {
                self.to_le_bytes()
            }
        }
    };
    ($($ty:ty;)*) => {
        $(
            impl_int_byte_repr!($ty);
        )*
    }
}

impl_int_byte_repr! {
    u8; u16; u32; u64; u128;
    i8; i16; i32; i64; i128;
}

#[derive(Debug, Error)]
pub enum LunBinError {
    #[error("io: {0}")]
    Io(#[from] std::io::Error),
    #[error("the file you provided isn't a .lb file, the magic numbers don't match")]
    MagicDontMatch,
    #[error("unknown file type {0:?}")]
    UnknownType(u8),
    #[error(
        "incompatible versions found {file_version}, but only support up to {compatible_version}."
    )]
    IncompatibleFileVersion {
        file_version: SmallVers,
        compatible_version: SmallVers,
    },
}

pub type Result<T, E = LunBinError> = std::result::Result<T, E>;

/// Shortened version of Semver, follows the same rules but with an implied
/// patch of 0
#[repr(C)]
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SmallVers {
    pub major: u16,
    pub minor: u16,
}

impl SmallVers {
    /// Latest version of LunBin
    pub const LATEST_LB_VERSION: SmallVers = SmallVers::LB_VERSION_0_1;

    /// Version 0.0
    pub const LB_VERSION_0_1: SmallVers = SmallVers { major: 0, minor: 1 };
}

impl Display for SmallVers {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}.{}", self.major, self.minor)
    }
}

impl ByteRepr<{ size_of::<Self>() }> for SmallVers {
    #[track_caller]
    fn from_bytes(bytes: [u8; Self::SIZE]) -> Self {
        assert_eq!(bytes.len(), size_of::<Self>());
        let major = u16::from_bytes_ref(&bytes[0..2]);
        let minor = u16::from_bytes_ref(&bytes[2..4]);

        SmallVers { major, minor }
    }

    fn as_bytes(&self) -> [u8; Self::SIZE] {
        let mut bytes = [0; 4];

        bytes[0..2].copy_from_slice(&self.major.as_bytes());
        bytes[2..4].copy_from_slice(&self.minor.as_bytes());

        bytes
    }
}

#[repr(C)]
#[derive(Debug, Clone)]
pub struct Version {
    pub major: u16,
    pub minor: u16,
    pub patch: u16,
}

impl Version {
    /// Latest version of LunBin
    pub const LUN_LATEST_VERSION: Version = Version::current();

    const fn current() -> Version {
        macro_rules! u16_from_env {
            ($name:tt) => {
                match u16::from_str_radix(env!($name), 10) {
                    Ok(v) => v,
                    Err(_) => panic!("unexpected error."),
                }
            };
        }
        Version {
            major: u16_from_env!("CARGO_PKG_VERSION_MAJOR"),
            minor: u16_from_env!("CARGO_PKG_VERSION_MINOR"),
            patch: u16_from_env!("CARGO_PKG_VERSION_PATCH"),
        }
    }
}

impl Display for Version {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}.{}.{}", self.major, self.minor, self.patch)
    }
}

impl ByteRepr<{ size_of::<Self>() }> for Version {
    #[track_caller]
    fn from_bytes(bytes: [u8; Self::SIZE]) -> Self {
        assert_eq!(bytes.len(), size_of::<Self>());
        let major = u16::from_bytes_ref(&bytes[0..2]);
        let minor = u16::from_bytes_ref(&bytes[2..4]);
        let patch = u16::from_bytes_ref(&bytes[4..6]);

        Version {
            major,
            minor,
            patch,
        }
    }

    fn as_bytes(&self) -> [u8; Self::SIZE] {
        let mut bytes = [0; 6];

        bytes[0..2].copy_from_slice(&self.major.as_bytes());
        bytes[2..4].copy_from_slice(&self.minor.as_bytes());
        bytes[4..6].copy_from_slice(&self.patch.as_bytes());

        bytes
    }
}

/// Type of LunBin
#[repr(u8)]
#[derive(Debug, Clone, Copy)]
pub enum LBType {
    /// Executable file
    Exec = 0,
    /// Static library
    Static = 1,
    /// Dynamic library
    Dyn = 2,
}

impl LBType {
    pub fn from_u8(val: u8) -> Result<LBType> {
        match val {
            0 => Ok(LBType::Exec),
            1 => Ok(LBType::Static),
            2 => Ok(LBType::Dyn),
            _ => Err(LunBinError::UnknownType(val)),
        }
    }
}

impl ByteRepr<{ size_of::<Self>() }> for LBType {
    #[track_caller]
    fn from_bytes(bytes: [u8; Self::SIZE]) -> Self {
        assert_eq!(bytes.len(), size_of::<Self>());
        LBType::from_u8(bytes[0]).unwrap()
    }

    fn as_bytes(&self) -> [u8; Self::SIZE] {
        [*self as u8]
    }
}

/// Header of LunBin
#[derive(Debug, Clone)]
pub struct LBHeader {
    /// "LUN\0" in ascii
    ///
    /// 4 bytes
    pub magic: [u8; 4],
    /// The version, used to decode the `lb` file
    ///
    /// 2 bytes
    pub fvers: SmallVers,
    /// Kind of LunBin
    ///
    /// 1 byte
    pub typ: LBType,
    /// Version of Lun when this LB was compiled
    ///
    /// 3 bytes
    pub lunvers: Version,
    /// Number of Sections
    ///
    /// 8 bytes
    pub sh_num: u64,
    /// Offset of the first Section in bytes
    ///
    /// 8 bytes
    pub sh_off: u64,
}

impl LBHeader {
    /// Magic numbers of LB, 4C 55 4E 00
    pub const MAGIC: [u8; 4] = *b"LUN\0";
}

/// A region specification
#[derive(Debug, Clone)]
pub struct SectionHeader {
    /// name of the region, stored as a local offset of the section `.shstr`
    pub name: u64,
    /// size in bytes of the section
    pub size: u64,
}

/// A lun blob is a file, that contains everything you need for a Lun library
/// or a Lun executable.
///
/// Numbers, everything in this file format is represented as little endian.
///
/// The file is organized as follows:
/// ```text
/// [magic][fvers][typ][lunvers][sh_num][sh_off][name][size][data...][name][size][data...] ...
/// |~~~~~~~~~~~~~~~~~ HEADER ~~~~~~~~~~~~~~~~~||~~~~ SECTION 1 ~~~~||~~~~ SECTION 2 ~~~~| ...
///                                             ^           <------->
///                                           sh_off          size
/// <------------------------------------------>                     <------------------->
///                HEADER SIZE: 31 bytes                         SECTION SIZE: 16 + size bytes
/// ```
///
/// where in the header:
/// - `magic`(4 bytes) is always 4C 55 4E 00
/// - `fvers`(2 x u16) the first for the major version and the second for the minor version of the file format
/// - `typ`(u8) that can have 3 values, 0, 1 and 2 for `Exec`, `Static` and `Dyn`
/// - `lunvers`(3 x u16), for major, minor and patch version of the Lun compiler when compiled
/// - `sh_num`(u64), the number of sections
/// - `sh_off`(u64), the offset from the start of the file, the 4C of the magic number to the first section.
///
/// and where in the sections,
/// - `name`(u64) is an offset in the `.shstr` section to the name of that section
/// - `size`(u64) is the size of the data in that section
/// - `data...`(size bytes) the raw data of the section
///
/// Common sections:
/// ```text
/// .code  : contains the blob bytecode.
/// .const : contains the constant pool
/// .cmap  : contains the map of the constants
/// .shstr : contains the section's name
/// .exec  : contains special information for "lb" file of type "Exec"
/// ```
///
/// Sections can be arranged in any order the do not need to be in a specific oreder.
#[derive(Debug, Clone)]
pub struct LunBin {
    /// Header of the LunBin File
    header: LBHeader,
    /// The data, where the regions are stored
    sections: Vec<(SectionHeader, Box<[u8]>)>,
}

impl LunBin {
    pub const MAGIC_SIZE: usize = 4;
    pub const FVERS_SIZE: usize = 4;
    pub const TYP_SIZE: usize = 1;
    pub const LUNVERS_SIZE: usize = 6;
    pub const SH_NUM_SIZE: usize = 8;
    pub const SH_OFF_SIZE: usize = 8;
    pub const SECTION_NAME_SIZE: usize = 8;
    pub const SECTION_SIZE_SIZE: usize = 8;

    pub const SECTION_CODE: &str = ".code";
    pub const SECTION_CONST: &str = ".const";
    pub const SECTION_CMAP: &str = ".cmap";
    pub const SECTION_SHSTR: &str = ".shstr";
    pub const SECTION_EXEC: &str = ".exec";

    pub fn serialize<W: Write>(&self, w: &mut W) -> Result<()> {
        // ===== HEADER =====

        // magic
        w.write_all(&self.header.magic)?;
        // fvers
        w.write_all(&self.header.fvers.as_bytes())?;
        // typ
        w.write_all(&self.header.typ.as_bytes())?;
        // lunvers
        w.write_all(&self.header.lunvers.as_bytes())?;
        // sh_num
        w.write_all(&self.header.sh_num.as_bytes())?;
        // sh_off
        w.write_all(&self.header.sh_off.as_bytes())?;

        // ===== SECTIONS =====
        for (sh, data) in &self.sections {
            // sh: name
            w.write_all(&sh.name.as_bytes())?;
            // sh: size
            w.write_all(&sh.size.as_bytes())?;

            assert_eq!(sh.size as usize, data.len());
            // data
            w.write_all(data)?;
        }

        Ok(())
    }

    pub fn deserialize<R: Read>(mut r: R) -> Result<LunBin> {
        let mut buf = vec![];
        r.read_to_end(&mut buf)?;

        let mut bin = LunBin {
            header: LBHeader {
                magic: LBHeader::MAGIC,
                fvers: SmallVers { major: 0, minor: 0 },
                typ: LBType::Exec,
                lunvers: Version {
                    major: 0,
                    minor: 0,
                    patch: 0,
                },
                sh_num: 0,
                sh_off: 0,
            },
            sections: vec![],
        };

        let mut offset = 0usize;
        let off = &mut offset;

        // ===== HEADER =====

        // magic numbers
        if read_off(&buf, off, Self::MAGIC_SIZE) != LBHeader::MAGIC {
            return Err(LunBinError::MagicDontMatch);
        }

        // fvers
        let fvers = SmallVers::from_bytes_ref(read_off(&buf, off, Self::FVERS_SIZE));
        if fvers != SmallVers::LATEST_LB_VERSION {
            // TODO: support deserializing from different versions.
            return Err(LunBinError::IncompatibleFileVersion {
                file_version: fvers.clone(),
                compatible_version: SmallVers::LATEST_LB_VERSION,
            });
        }
        bin.header.fvers = fvers;

        // typ
        let typ = LBType::from_u8(read_off(&buf, off, Self::TYP_SIZE)[0])?;
        bin.header.typ = typ;

        // lunvers
        let lunvers = Version::from_bytes_ref(read_off(&buf, off, Self::LUNVERS_SIZE));
        bin.header.lunvers = lunvers;

        // sh_num
        let sh_num = u64::from_bytes_ref(read_off(&buf, off, Self::SH_NUM_SIZE));
        bin.header.sh_num = sh_num;

        // sh_off
        let sh_off = u64::from_bytes_ref(read_off(&buf, off, Self::SH_OFF_SIZE));
        bin.header.sh_off = sh_off;

        // ===== SECTIONS =====
        *off = sh_off as usize;

        for _ in 0..sh_num {
            let name = u64::from_le_bytes(
                read_off(&buf, off, Self::SECTION_NAME_SIZE)
                    .try_into()
                    .unwrap(),
            );
            let size = u64::from_le_bytes(
                read_off(&buf, off, Self::SECTION_SIZE_SIZE)
                    .try_into()
                    .unwrap(),
            );
            let data = read_off(&buf, off, size as usize);
            let boxed_data = Box::from(data);

            bin.sections
                .push((SectionHeader { name, size }, boxed_data));
        }

        Ok(bin)
    }

    /// Dump as human readable content to stdout
    pub fn dump(&self) {
        println!("----- LUN BIN -----");
        println!("HEADER:");
        println!("  fvers:   {}", self.header.fvers);
        println!("  typ:     {:?}", self.header.typ);
        println!("  lunvers: {}", self.header.lunvers);
        println!("  sh_num:  {}", self.header.sh_num);
        println!("  sh_off:  {:X}", self.header.sh_off);

        let mut i = 0;
        let name_data = loop {
            if self.sections[i].0.name == 0 {
                break self.sections[i].1.clone();
            }
            i += 1;
        };
        let names = String::from_utf8_lossy(&name_data);

        println!();

        for (sh, data) in &self.sections {
            let off = sh.name as usize + 8;
            let size =
                u64::from_bytes_ref(&name_data[sh.name as usize..sh.name as usize + 8]) as usize;

            let name = &names[off..off + size];
            println!("SECTION {}", name);
            match name {
                ".code" => {
                    let blob = BcBlob {
                        code: data.clone().into(),
                        dpool: DataPool::new(),
                    };
                    blob.disassemble("");
                }
                ".cmap" => {
                    let mut i = 0;
                    let mut off = 0;
                    loop {
                        let offset = u64::from_bytes_ref(&data[off..off + 8]);
                        let size = u64::from_bytes_ref(&data[(off + 8)..(off + 16)]);
                        println!("const {i:04}: offset={offset:X?}, size={size:?}");
                        i += 1;
                        off += 8 * 2;

                        if off >= data.len() {
                            break;
                        }
                    }
                }
                _ => {
                    if data.len() < 32 {
                        println!("{:?}", data);
                    } else {
                        println!("[... {} bytes]", data.len());
                    }
                }
            }
            println!();
        }
    }
}

// TODO: make this function's `size` paramter constant, so we can return an array
pub(crate) fn read_off<'a>(buf: &'a [u8], off: &'a mut usize, size: usize) -> &'a [u8] {
    let res = &buf[*off..(*off + size)];
    *off += size;
    res
}

#[derive(Debug, Clone)]
struct NotBuildSection {
    name: String,
    data: Vec<u8>,
}

/// A lun bin builder that builds lun bins with the latest `fvers`
#[derive(Debug, Clone)]
pub struct LunBinBuilder {
    typ: Option<LBType>,
    sections: Vec<NotBuildSection>,
}

impl LunBinBuilder {
    pub fn new() -> LunBinBuilder {
        LunBinBuilder {
            typ: None,
            sections: Vec::new(),
        }
    }

    pub fn typ(&mut self, typ: LBType) {
        self.typ = Some(typ);
    }

    pub fn section(&mut self, name: impl ToString, data: Vec<u8>) {
        self.sections.push(NotBuildSection {
            name: name.to_string(),
            data,
        });
    }

    pub fn build(self) -> Option<LunBin> {
        // TODO: add the generation of the `.exec` section
        // ===== HEADER =====
        let magic = LBHeader::MAGIC;
        let fvers = SmallVers::LATEST_LB_VERSION;
        let typ = self.typ?;
        let lunvers = Version::LUN_LATEST_VERSION;
        let sh_num = self.sections.len() as u64;
        let sh_off = 31;

        // ===== SECTION =====
        let mut sections = Vec::new();

        // In .shstr, strings are stored as follows:
        // the lenght in bytes of the string is first represented as a u64
        // then the string with the given length
        let mut shstr = Vec::<u8>::new();

        fn write_shstr(shstr: &mut Vec<u8>, str: impl ToString) -> usize {
            let str = str.to_string();

            let off = shstr.len();
            // TODO: implement ByteRepr for String but make ByteRepr use runtime sizes
            shstr.write_all(&(str.len() as u64).as_bytes()).unwrap();
            shstr.write_all(&str.into_bytes()).unwrap();
            off
        }

        // `.shstr` must be the first name in `.shstr`.
        let shstr_name = write_shstr(&mut shstr, LunBin::SECTION_SHSTR) as u64;

        for section in self.sections {
            let name = write_shstr(&mut shstr, section.name) as u64;

            sections.push((
                SectionHeader {
                    name,
                    size: section.data.len() as u64,
                },
                section.data.into_boxed_slice(),
            ));
        }

        sections.push((
            SectionHeader {
                name: shstr_name,
                size: shstr.len() as u64,
            },
            shstr.into_boxed_slice(),
        ));

        Some(LunBin {
            header: LBHeader {
                magic,
                fvers,
                typ,
                lunvers,
                sh_num,
                sh_off,
            },
            sections,
        })
    }
}
