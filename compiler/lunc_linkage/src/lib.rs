//! Takes the object file from the codegen, and outputs a file with the format
//! corresponding to the orb type.
#![doc(
    html_logo_url = "https://raw.githubusercontent.com/lunprog/lun/main/src/assets/logo_no_bg_black.png"
)]

use std::{
    fs::File,
    io::{self, Write},
    path::{Path, PathBuf},
    process::{Command, Output},
};

use lunc_utils::{BuildOptions, OrbType};
use tempfile::{Builder, NamedTempFile};

/// Takes the object file and turns it into the file with appropriate format for
/// the orb type.
#[derive(Debug)]
pub struct Linker {
    /// object content
    objbytes: Vec<u8>,
    /// path of the object file
    objpath: Option<PathBuf>,
    /// output path with the extension
    out: PathBuf,
    /// tempfile, used when we don't want to output .o file.
    ///
    /// # Note
    ///
    /// This is used to keep the temporary file alive, so that the linker can
    /// still find the object file before it being deleted.
    tempfile: Option<NamedTempFile>,
    /// linker output
    linker_out: Option<Output>,
    /// build options
    opts: BuildOptions,
}

impl Linker {
    /// Create a new linker
    pub fn new(
        objbytes: Vec<u8>,
        objpath: Option<PathBuf>,
        out: impl AsRef<Path>,
        opts: BuildOptions,
    ) -> Linker {
        Linker {
            objbytes,
            objpath,
            out: out.as_ref().to_path_buf(),
            tempfile: None,
            linker_out: None,
            opts,
        }
    }

    /// Perform the linkage, this function must be called after
    /// [`Linker::write_obj`] was called.
    pub fn link(&mut self) -> io::Result<()> {
        match self.opts.orb_type() {
            OrbType::Bin => self.link_bin(),
            _ => todo!(),
        };

        Ok(())
    }

    /// Write the object file to the filesystem, either in a temporary file or
    /// in a defined path
    pub fn write_obj(&mut self) -> io::Result<()> {
        if let Some(path) = &self.objpath {
            let mut file = File::create(path)?;

            file.write_all(&self.objbytes)?;

            Ok(())
        } else {
            let mut named_tempfile = Builder::new()
                .prefix("lunc_")
                .suffix(".o")
                .rand_bytes(8)
                .tempfile()?;

            self.objpath = Some(named_tempfile.path().to_path_buf());

            named_tempfile.write_all(&self.objbytes)?;

            self.tempfile = Some(named_tempfile);

            Ok(())
        }
    }

    fn link_bin(&mut self) {
        let mut cmd = Command::new("cc");

        cmd.arg("-o")
            .arg(&self.out)
            .arg(self.objpath.as_deref().unwrap()) // we set it in write_obj, unwrapping is fine.
            .arg("-nodefaultlibs")
            .arg("-lc")
            .arg("-pie");

        self.linker_out = Some(cmd.output().expect("failed to run the linker"));
    }

    /// Takes the output of the linker.
    #[track_caller]
    pub fn linker_out(&mut self) -> Output {
        self.linker_out.take().unwrap()
    }
}
