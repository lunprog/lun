//! Lun is a staticaly typed programming language.

use std::{env, fs::read_to_string, io, path::PathBuf, process::ExitCode, str::FromStr};

use lunc_parser::Parser;
use shadow_rs::shadow;
use thiserror::Error;

use crate::{
    diag::{DiagnosticSink, StageResult},
    lexer::Lexer,
    utils::pluralize,
};

pub use lunc_codegen as codegen;
pub use lunc_diag as diag;
pub use lunc_fir as fir;
pub use lunc_lexer as lexer;
pub use lunc_parser as parser;
pub use lunc_semack as semack;
pub use lunc_utils as utils;

shadow!(build);

type Result<T, E = CliError> = std::result::Result<T, E>;

pub fn exit_code_compilation_failed() -> ExitCode {
    ExitCode::from(101)
}

macro_rules! tri {
    ($expr:expr, $sink:expr) => {
        match $expr {
            StageResult::Good(val) => val,
            StageResult::Part(val, sink) => {
                $sink.merge(sink);
                val
            }
            StageResult::Fail(sink) => {
                return Err(CliError::CompilerDiagnostics { sink });
            }
        }
    };
}

#[derive(Debug, Error)]
pub enum CliError {
    /// Diagnostics emited in compilation, can contain only warnings, can
    /// contain errors. It is guaranteed to contains at least one diag
    #[error("Compiler diagnostics, {}", sink.summary().unwrap())]
    CompilerDiagnostics { sink: DiagnosticSink },
    #[error(
        "argument to '{name}' is missing, expected {expected} value{}",
        pluralize(*expected)
    )]
    ArgumentsMissing { name: String, expected: usize },
    #[error("unrecognized command-line option `{arg}`")]
    UnreochizedOption { arg: String },
    #[error("no input file")]
    NoInputFile,
    #[error("the argument `{arg}` is used multiple times")]
    ArgumentUsedMultipleTimes { arg: String },
    #[error("unknown value `{value}` for argument `{arg}`")]
    UnknownValue { arg: String, value: String },
    #[error("{path}: {err}")]
    FileIoError { path: PathBuf, err: io::Error },
}

pub const HELP_MESSAGE: &str = "\
Compiler for the Lun Programming Language.

Usage: lunc [OPTIONS] INPUT

Options:
    -h, -help                Display this help message
    -o <file>                Place the output into <file>, defaults to the file
                             with the correct file extension
    -D<flag>[=value]         Debug flags, type `lunc -Dhelp` for details
        -target <triple>     Compile for the given target, type `lunc -target
                             help` for details
    -V, -version             Print version information
    -v, -verbose             Make the output verbose\
";

pub const DEBUG_FLAGS_HELP: &str = "\
Debug flags help:
-Dhelp                       Display this message
-Dhalt-at=<stage>            Halts the compilation after <stage>, one of:
                             * lexer
                             * parser
                             * dir
                             * tir
                             * fir
                             * codegen
-Dprint=<value>              Prints to the standard error, one or more of:
                             * inputfile
                             * tokentree
                             * ast
                             * dir-tree
                             * tir-tree
                             * fir-tree
                             * fir
                             * asm\
";

// TODO: add support for bare metal targets like `x86_64-none-elf`
pub const TARGET_HELP: &str = "\
Target format: <arch><[sub]>-<sys>-<env> where:
- arch = `x64_64`, `arm`, `arm64`, `riscv64`, `riscv32`
- sub  = for eg, riscv64 = `imaf`, `g`, `gc`
- sys  = `linux`, `windows`, `android`, `darwin`
- env  = `gnu`, `msvc`, `elf`, `macho`

List of supported targets:
- x86_64-linux-gnu\
";

/// Debug flags
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum DebugFlag {
    HaltAt(DebugHalt),
    Print(DebugPrint),
    /// Prints the debug flag help message
    Help,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum DebugHalt {
    Lexer,
    Parser,
    Dir,
    Tir,
    Fir,
    Codegen,
}

impl FromStr for DebugHalt {
    type Err = CliError;

    fn from_str(s: &str) -> Result<Self> {
        use DebugHalt as Hs;

        match s {
            "lexer" => Ok(Hs::Lexer),
            "parser" => Ok(Hs::Parser),
            "dir" => Ok(Hs::Dir),
            "tir" => Ok(Hs::Tir),
            "fir" => Ok(Hs::Fir),
            "codegen" => Ok(Hs::Codegen),
            _ => Err(CliError::UnknownValue {
                value: s.to_string(),
                arg: "-Dhalt-at".to_string(),
            }),
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DebugPrint {
    InputFile,
    TokenTree,
    Ast,
    DirTree,
    TirTree,
    FirTree,
    Fir,
    Asm,
}

impl FromStr for DebugPrint {
    type Err = CliError;

    fn from_str(s: &str) -> Result<Self> {
        use DebugPrint as Dp;

        match s {
            "inputfile" => Ok(Dp::InputFile),
            "tokentree" => Ok(Dp::TokenTree),
            "ast" => Ok(Dp::Ast),
            "dir-tree" => Ok(Dp::DirTree),
            "tir-tree" => Ok(Dp::TirTree),
            "fir-tree" => Ok(Dp::FirTree),
            "fir" => Ok(Dp::Fir),
            "asm" => Ok(Dp::Asm),
            _ => Err(CliError::UnknownValue {
                value: s.to_string(),
                arg: "-Dprint".to_string(),
            }),
        }
    }
}

/// Arguments to the `lunc` binary
#[derive(Debug, Clone, Default)]
pub struct CliArgs {
    /// print the help message?
    help: bool,
    /// input file
    input: PathBuf,
    /// output file
    output: Option<PathBuf>,
    /// debug flags
    debug: Vec<DebugFlag>,
    /// true if we want to print the version
    version: bool,
    /// verbosity
    verbose: bool,
}

impl CliArgs {
    pub fn parse_args(mut args: impl Iterator<Item = String>) -> Result<CliArgs> {
        // skip program name
        _ = args.next();

        let mut output = None;
        let mut debug = Vec::new();
        let mut verbose = true;
        let mut input = None;
        let mut version = false;
        let mut help = false;

        while let Some(arg) = args.next() {
            if arg == "-h" || arg == "-help" {
                help = true;
            } else if arg == "-o" {
                if let Some(path) = args.next() {
                    output = Some(PathBuf::from(path));
                } else {
                    return Err(CliError::ArgumentsMissing {
                        name: String::from("-o"),
                        expected: 1,
                    });
                }
            } else if arg.starts_with("-D") {
                // Debug flags
                let flag_value = &arg[2..];
                let splits = flag_value.rsplit_once("=");
                match splits {
                    Some(("halt-at", stage)) => {
                        for dbg in &debug {
                            if let DebugFlag::HaltAt(_) = dbg {
                                return Err(CliError::ArgumentUsedMultipleTimes { arg });
                            }
                        }
                        debug.push(DebugFlag::HaltAt(stage.parse()?));
                    }
                    Some(("print", value)) => debug.push(DebugFlag::Print(value.parse()?)),
                    None if flag_value == "help" => {
                        debug.push(DebugFlag::Help);
                    }
                    _ => return Err(CliError::UnreochizedOption { arg }),
                }
            } else if arg == "-target" {
                todo!("create a target type and a parsing function for it.")
            } else if arg == "-V" || arg == "-version" {
                version = true;
            } else if arg == "-v" || arg == "-verbose" {
                verbose = true;
            } else if input.is_none() && !arg.starts_with("-") {
                input = Some(PathBuf::from(arg));
            } else {
                return Err(CliError::UnreochizedOption { arg });
            }
        }

        let Some(input) = input else {
            if version || help || debug.contains(&DebugFlag::Help) {
                return Ok(CliArgs {
                    help,
                    input: Default::default(),
                    output,
                    debug,
                    version,
                    verbose,
                });
            }
            return Err(CliError::NoInputFile);
        };

        Ok(CliArgs {
            help,
            input,
            output,
            debug,
            version,
            verbose,
        })
    }

    /// Return true if one of the debug flags is `-Dhelp`
    pub fn debug_flag_help(&self) -> bool {
        self.debug.contains(&DebugFlag::Help)
    }

    /// Return true if one of the debug flags is `-Dprint=VALUE`
    pub fn debug_print_at(&self, value: DebugPrint) -> bool {
        self.debug.contains(&DebugFlag::Print(value))
    }

    /// Return true if one of the debug flags is `-Dhalt-at=STAGE`
    pub fn debug_halt_at(&self, stage: DebugHalt) -> bool {
        self.debug.contains(&DebugFlag::HaltAt(stage))
    }
}

pub fn run() -> Result<()> {
    let argv = CliArgs::parse_args(env::args())?;

    // maybe print help message
    if argv.help {
        eprintln!("{HELP_MESSAGE}");
        return Ok(());
    }

    // maybe print version
    if argv.version {
        eprintln!(
            "lunc {version} ({commit} {date})",
            version = env!("CARGO_PKG_VERSION"),
            commit = build::SHORT_COMMIT,
            date = &build::COMMIT_DATE[..10]
        );

        if argv.verbose {
            // TODO: print the host target
            eprintln!("commit-hash: {}", build::COMMIT_HASH);
            eprintln!("commit-date: {}", build::COMMIT_DATE);
            eprintln!("rustc-version: {}", build::RUST_VERSION);
            eprintln!("rustc-toolchain: {}", build::RUST_CHANNEL);
        }
        return Ok(());
    }

    // maybe print debug flag help
    if argv.debug_flag_help() {
        eprintln!("{DEBUG_FLAGS_HELP}");
        return Ok(());
    }

    // 1. retrieve the source code
    let source_code = read_to_string(&argv.input).map_err(|err| CliError::FileIoError {
        path: argv.input.clone(),
        err,
    })?;

    //    maybe print source code
    if argv.debug_print_at(DebugPrint::InputFile) {
        eprintln!("{source_code}");
    }

    // 2. create the diagnostic sink
    let input_str = argv.input.clone().into_os_string().into_string().unwrap();
    let mut sink = DiagnosticSink::new(input_str, source_code.clone());

    // 3. lex the file
    let mut lexer = Lexer::new(sink.clone(), source_code);
    let tokentree = tri!(lexer.produce(), sink);

    //    maybe print the token tree
    if argv.debug_print_at(DebugPrint::TokenTree) {
        eprintln!("tokentree = {:#?}", tokentree);
    }
    if argv.debug_halt_at(DebugHalt::Lexer) {
        return Ok(());
    }

    // 4. parse the token tree to an ast
    let mut parser = Parser::new(tokentree, sink.clone());
    let ast = tri!(parser.produce(), sink);

    //    maybe print the ast
    if argv.debug_print_at(DebugPrint::Ast) {
        eprintln!("ast = {:#?}", ast);
    }
    if argv.debug_halt_at(DebugHalt::Parser) {
        return Ok(());
    }

    Ok(())
}
