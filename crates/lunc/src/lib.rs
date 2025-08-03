//! Lun is a statically typed programming language.

use std::{
    env,
    fs::read_to_string,
    io::{self, Write, stderr},
    path::PathBuf,
    process::ExitCode,
    str::FromStr,
};

use thiserror::Error;

use crate::{
    diag::{DiagnosticSink, FileId},
    dsir::Desugarrer,
    lexer::Lexer,
    parser::Parser,
    scir::SemaChecker,
    utils::{
        pluralize,
        pretty::PrettyDump,
        target::{TargetParsingError, TargetTriplet},
    },
};

mod re_exports {
    #[doc(inline)]
    pub use lunc_codegen as codegen;

    #[doc(inline)]
    pub use lunc_diag as diag;

    #[doc(inline)]
    pub use lunc_dsir as dsir;

    #[doc(inline)]
    pub use lunc_fir as fir;

    #[doc(inline)]
    pub use lunc_lexer as lexer;

    #[doc(inline)]
    pub use lunc_parser as parser;

    #[doc(inline)]
    pub use lunc_scir as scir;

    #[doc(inline)]
    pub use lunc_utils as utils;
}

#[doc(inline)]
pub use re_exports::*;

mod build {
    use shadow_rs::shadow;
    shadow!(build);

    pub use build::*;
}

type Result<T, E = CliError> = std::result::Result<T, E>;

pub fn exit_code_compilation_failed() -> ExitCode {
    ExitCode::from(101)
}

#[derive(Debug, Error)]
pub enum CliError {
    /// Diagnostics emitted in compilation, can contain only warnings, can
    /// contain errors. It is guaranteed to contains at least one diag
    #[error("Compiler diagnostics, {}", sink.summary(orb_name).unwrap())]
    CompilerDiagnostics {
        sink: DiagnosticSink,
        orb_name: String,
    },
    #[error(
        "argument to '{name}' is missing, expected {expected} value{}",
        pluralize(*expected)
    )]
    ArgumentsMissing { name: String, expected: usize },
    #[error("unrecognized command-line option `{arg}`")]
    UnreochizedOption { arg: String },
    #[error("no input file")]
    NoInputFile,
    #[error("the argument '{arg}' is used multiple times")]
    ArgumentUsedMultipleTimes { arg: String },
    #[error("unknown value '{value}' for argument '{arg}'")]
    UnknownValue { arg: String, value: String },
    #[error("{path}: {err}")]
    FileIoError { path: PathBuf, err: io::Error },
    #[error(transparent)]
    TargetParsingError(#[from] TargetParsingError),
    #[error("unsupported target: '{target}', type 'lunc -target help' for details")]
    UnsupportedTargetTriplet { target: TargetTriplet },
}

pub const HELP_MESSAGE: &str = "\
Compiler for the Lun Programming Language.

Usage: lunc [OPTIONS] INPUT

Options:
    -h, -help                Display this help message
    -o <file>                Place the output into <file>, defaults to the orb's
                             name with the correct file extension for the target.
    -D<flag>[=value]         Debug flags, type `lunc -Dhelp` for details
        -target <triplet>    Build for the given target triplet, type `lunc
                             -target help` for details
        -orb-name <name>     Specify the name of the orb being built, defaults
                             to the input file name with the extension
    -V, -version             Print version information
    -v, -verbose             Make the output verbose\
";

pub const DEBUG_FLAGS_HELP: &str = "\
Debug flags help:
-Dhelp                       Display this message
-Dhalt-at=<stage>            Halts the compilation after <stage>, one of:
                             * lexer
                             * parser
                             * dsir
                             * scir
                             * fir
                             * codegen
-Dprint=<value>              Prints to the standard error, one or more of:
                             * inputfile
                             * tokenstream
                             * ast
                             * dsir-tree
                             * scir-tree
                             * fir-tree
                             * fir
                             * asm\
";

pub fn target_help(out: &mut impl Write) {
    const TARGET_HELP: &str = "\
Target format: <arch><[sub]>-<sys>-<env> where:
- arch = `x86_64`, `x86`, `arm`, `aarch64`, `riscv64`, `riscv32`
- sub  = for eg, riscv64 = `imaf`, `g`, `gc`
- sys  = `linux`, `windows`, `android`, `macos`, `none`
- env  = `gnu`, `msvc`, `elf`, `macho`

List of supported targets:\
";
    writeln!(out, "{TARGET_HELP}").unwrap();

    for target in TargetTriplet::SUPPORTED_TARGETS {
        writeln!(out, "{target}").unwrap();
    }
}

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
    Dsir,
    Scir,
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
            "dsir" => Ok(Hs::Dsir),
            "scir" => Ok(Hs::Scir),
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
    TokenStream,
    Ast,
    DsirTree,
    ScirTree,
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
            "tokenstream" => Ok(Dp::TokenStream),
            "ast" => Ok(Dp::Ast),
            "dsir-tree" => Ok(Dp::DsirTree),
            "scir-tree" => Ok(Dp::ScirTree),
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

#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub enum TargetInput {
    /// the user specified nothing
    #[default]
    Unspecified,
    /// the user wants to print the help message for the targets
    Help,
    /// there is a specified target
    Triplet(TargetTriplet),
}

// TODO: add -orb-type <type> arg
/// Arguments to the `lunc` binary
#[derive(Debug, Clone, Default)]
pub struct CliArgs {
    /// print the help message?
    help: bool,
    /// input file
    input: PathBuf,
    /// output file
    output: PathBuf,
    /// debug flags
    debug: Vec<DebugFlag>,
    /// target
    target: TargetInput,
    /// the name of the orb you are building
    orb_name: String,
    /// true if we want to print the version
    version: bool,
    /// verbosity
    verbose: bool,
}

impl CliArgs {
    /// Parse the arguments
    pub fn parse_args(mut args: impl Iterator<Item = String>) -> Result<CliArgs> {
        // skip program name
        _ = args.next();

        let mut input = None;
        let mut help = false;
        let mut output = None;
        let mut debug = Vec::new();
        let mut target = TargetInput::default();
        let mut orb_name = None;
        let mut version = false;
        let mut verbose = false;

        while let Some(arg) = args.next() {
            if arg == "-h" || arg == "-help" {
                help = true;
            } else if arg == "-o" {
                output = Some(PathBuf::from(CliArgs::next_arg(&mut args)?));
            } else if let Some(flag_value) = arg.strip_prefix("-D") {
                // Debug flags
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
                let target_str = CliArgs::next_arg(&mut args)?;
                match target_str.as_str() {
                    "help" => target = TargetInput::Help,
                    s => target = TargetInput::Triplet(TargetTriplet::from_str(s)?),
                }
            } else if arg == "-orb-name" {
                // TODO: check that the name can be a Lun identifier.
                orb_name = Some(CliArgs::next_arg(&mut args)?);
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
            if version || help || target == TargetInput::Help || debug.contains(&DebugFlag::Help) {
                return Ok(CliArgs {
                    help,
                    input: Default::default(),
                    output: output.unwrap_or_default(),
                    debug,
                    target,
                    orb_name: Default::default(),
                    version,
                    verbose,
                });
            }
            return Err(CliError::NoInputFile);
        };

        let orb_name = orb_name.unwrap_or(input.with_extension("").to_string_lossy().to_string());
        let output = output.unwrap_or(PathBuf::from(orb_name.as_str()));

        Ok(CliArgs {
            help,
            input,
            output,
            debug,
            target,
            orb_name,
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

    fn next_arg(args: &mut impl Iterator<Item = String>) -> Result<String> {
        args.next().ok_or_else(|| CliError::ArgumentsMissing {
            name: String::from("-o"),
            expected: 1,
        })
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
            eprintln!("host: {}", TargetTriplet::host_target());
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

    // maybe print the target help message
    if argv.target == TargetInput::Help {
        target_help(&mut stderr());
        return Ok(());
    }

    if let TargetInput::Triplet(ref target) = argv.target
        && !TargetTriplet::SUPPORTED_TARGETS.contains(target)
    {
        return Err(CliError::UnsupportedTargetTriplet {
            target: target.clone(),
        });
    }

    // 1. retrieve the source code, file => text
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
    let sink = DiagnosticSink::new();
    let root_fid = sink.register_file(input_str, source_code.clone());
    assert_eq!(root_fid, FileId::ROOT_MODULE);

    let orb_name = argv.orb_name.clone();

    let compil_diags = || CliError::CompilerDiagnostics {
        sink: sink.clone(),
        orb_name: orb_name.clone(),
    };

    // 3. lexing, text => token stream
    let mut lexer = Lexer::new(sink.clone(), source_code.clone(), root_fid);
    let tokenstream = lexer.produce().ok_or_else(compil_diags)?;

    //    maybe print the token stream
    if argv.debug_print_at(DebugPrint::TokenStream) {
        eprint!("tokenstream = ");
        tokenstream.fmt(&mut stderr(), &source_code).unwrap();
    }
    if argv.debug_halt_at(DebugHalt::Lexer) {
        if sink.is_empty() {
            return Ok(());
        } else {
            return Err(CliError::CompilerDiagnostics { sink, orb_name });
        }
    }

    // 4. parsing, token stream => AST
    let mut parser = Parser::new(tokenstream, sink.clone(), root_fid);
    let ast = parser.produce().ok_or_else(compil_diags)?;

    //    maybe print the ast
    if argv.debug_print_at(DebugPrint::Ast) {
        eprint!("ast = ");
        ast.dump();
        eprintln!();
    }
    if argv.debug_halt_at(DebugHalt::Parser) {
        if sink.is_empty() {
            return Ok(());
        } else {
            return Err(CliError::CompilerDiagnostics { sink, orb_name });
        }
    }

    // 5. desugarring, AST => DSIR
    let mut desugarrer = Desugarrer::new(sink.clone(), argv.orb_name.clone());
    let dsir = desugarrer.produce(ast).ok_or_else(compil_diags)?;

    //    maybe print the DSIR
    if argv.debug_print_at(DebugPrint::DsirTree) {
        eprint!("dsir = ");
        dsir.dump();
        eprintln!();
    }
    if argv.debug_halt_at(DebugHalt::Dsir) {
        if sink.is_empty() {
            return Ok(());
        } else {
            return Err(CliError::CompilerDiagnostics { sink, orb_name });
        }
    }

    // 6. type-checking and all the semantic analysis, DSIR => SCIR
    let mut semacker = SemaChecker::new(sink.clone());
    let scir = semacker.produce(dsir).ok_or_else(compil_diags)?;

    //    maybe print the SCIR
    if argv.debug_print_at(DebugPrint::ScirTree) {
        eprint!("scir = ");
        scir.dump();
        eprintln!();
    }
    if argv.debug_halt_at(DebugHalt::Scir) {
        if sink.is_empty() {
            return Ok(());
        } else {
            return Err(CliError::CompilerDiagnostics { sink, orb_name });
        }
    }

    // use output to remove the warning
    _ = argv.output;

    if sink.is_empty() {
        Ok(())
    } else {
        Err(CliError::CompilerDiagnostics { sink, orb_name })
    }
}
