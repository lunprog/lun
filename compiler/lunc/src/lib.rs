//! Lun is a statically typed programming language.
//!
//! Related crates of the compiler:
//! - [lunc_lexer], lexes the text into [Tokens]
//! - [lunc_parser], parses the [Tokens] into an [Ast]
//! - [lunc_dsir], desugars the [Ast] to [Dsir] and resolve names
//! - [lunc_scir], lowers [Dsir] to [Scir] and perform various semantic checks
//!   and add types
//! - [lunc_cranelift_codegen], generates the Cranelift IR from [Scir]
//! - [lunc_diag], the error handling, the diagnostic system, with the Sink.
//! - [lunc_utils], various internal utilities of the compiler
//!
//! [Tokens]: lunc_utils::token::TokenStream
//! [Ast]: lunc_parser::item::Module
//! [Dsir]: lunc_dsir::DsModule
//! [Scir]: lunc_scir::ScModule
#![doc(
    html_logo_url = "https://raw.githubusercontent.com/lunprog/lun/main/src/assets/logo_no_bg_black.png"
)]

use clap::{ArgAction, Parser as ArgParser, ValueEnum};
use std::{
    backtrace::{Backtrace, BacktraceStatus},
    env,
    error::Error,
    fmt::{self, Write},
    fs::{self, read_to_string},
    io::{self, Write as IoWrite, stderr},
    panic,
    path::PathBuf,
    process::{ExitCode, abort},
    str::FromStr,
    thread,
    time::{Duration, Instant},
};
use termcolor::{ColorChoice, ColorChoiceParseError, StandardStream};
use thiserror::Error;

use lunc_cranelift_codegen::{ClifGen, ClifGenContext, OptLevel};
use lunc_diag::{DiagnosticSink, FileId};
use lunc_dsir::Desugarrer;
use lunc_lexer::Lexer;
use lunc_parser::Parser;
use lunc_scir::SemaChecker;
use lunc_utils::{
    BuildOptions, is_identifier,
    pretty::PrettyDump,
    target::{self, Triple},
};

mod build {
    use shadow_rs::shadow;
    shadow!(build);

    pub use build::*;
}

type Result<T, E = CliError> = std::result::Result<T, E>;

pub fn exit_code_compilation_failed() -> ExitCode {
    ExitCode::from(255)
}

#[derive(Debug, Error)]
pub enum CliError {
    /// Diagnostics emitted in compilation, can contain only warnings or errors.
    /// It is guaranteed to contains at least one diag
    #[error("build diagnostic(s)")]
    BuildDiagnostics { failed: bool },
    #[error("{path}: {err}")]
    FileIoError { path: PathBuf, err: io::Error },
    #[error(transparent)]
    TargetParsingError(#[from] target::ParseError),
    #[error("unsupported target: '{target}', type 'lunc --target help' for details")]
    UnsupportedTriple { target: target::Triple },
    #[error("the orb name must be a valid identifier but got {orb_name:?}.")]
    NonIdentifierOrbName { orb_name: String },
    #[error(transparent)]
    Dyn(#[from] Box<dyn Error>),
    #[error(transparent)]
    ColorChoiceParseError(#[from] ColorChoiceParseError),
    #[error("no input file")]
    NoInputFile,
    #[error("the argument '{0}' is used multiple times")]
    ArgumentUsedMultipleTimes(String),
    #[error(transparent)]
    ClapError(#[from] clap::Error),
    #[error("invalid value ({0}) for -Z halt, for more details `lunc -Z help`")]
    InvalidHaltVal(String),
    #[error("invalid value ({0}) for -Z timings, possible values: `true`,`false`")]
    InvalidTimingsVal(String),
    #[error("invalid value ({0}) for -Z print, for more details `lunc -Z help`")]
    InvalidPrintVal(String),
    #[error("invalid value ({0}) for -C opt-level, for more details `lunc -C help`")]
    InvalidOptLevelVal(String),
    #[error("invalid value ({0}) for -C output-obj, for more details `lunc -C help`")]
    InvalidOutputObjVal(String),
}

pub fn flush_outs() {
    io::stderr().flush().expect("can't flush stderr");
    io::stdout().flush().expect("can't flush stdout");
}

/// Lunc Cli args.
#[derive(ArgParser, Debug)]
#[command(
    about = "Compiler for the Lun Programming Language.",
    disable_version_flag = true
)]
pub struct RawLuncCli {
    /// Specify the name of the orb being built, defaults to the input file
    /// name with the extension
    #[arg(short = 'o', long)]
    output: Option<PathBuf>,

    /// The root file of the orb to build.
    input: Option<PathBuf>,

    /// Debug options, type `lunc -Z help` for some help.
    #[arg(short = 'Z', value_name = "OPT=VAL")]
    debug: Vec<Kv<DebugKey, String>>,

    /// Build for the given target triplet, type `lunc --target help` for more
    /// details
    #[arg(long)]
    target: Option<String>,

    /// Name of the orb, defaults to the input file name with the extension
    #[arg(long)]
    orb_name: Option<String>,

    /// Coloring possible values: 'always', 'always-ansi', 'never' and 'auto'
    #[arg(long, default_value_t = String::from("auto"))]
    color: String,

    /// Codegen options, type `lunc -C help` for some help.
    #[arg(short = 'C', long, value_name = "OPT=VAL")]
    codegen: Vec<Kv<CodegenKey, String>>,

    /// Print version info and exit
    #[arg(short = 'V', long, action = ArgAction::SetTrue)]
    version: bool,

    /// Verbosity flag
    #[arg(short = 'v', long, action = ArgAction::SetTrue)]
    verbose: bool,
}

/// Key-value pair for `-Z` like options
#[derive(Debug, Clone)]
pub struct Kv<K: ValueEnumExt, V: FromStr> {
    pub key: K,
    pub val: V,
}

impl<K: ValueEnumExt> FromStr for Kv<K, String> {
    type Err = String;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let mut splits = s.split('=');

        let key = splits.next().ok_or_else(|| "expected a key".to_string())?;
        if key == "help" {
            return Ok(Kv {
                key: K::help(),
                val: String::new(),
            });
        }

        let val = splits
            .next()
            .ok_or_else(|| "missing `=` in OPT=VAL".to_string())?
            .to_string();

        Ok(Kv {
            key: K::from_str(key, false)?,
            val,
        })
    }
}

pub trait ValueEnumExt: ValueEnum + PartialEq {
    /// Create a new help variant
    fn help() -> Self;

    /// Name of the value enum
    fn name() -> &'static str;

    /// Get the rest of the help message for variant if any.
    fn help_extended(variant: &str) -> Option<&'static str>;

    fn is_help(&self) -> bool {
        *self == Self::help()
    }

    fn help_msg() -> String {
        let mut help = String::new();

        writeln!(help, "{} options help:", Self::name()).unwrap();

        let mut width = 0;

        for variant in Self::value_variants() {
            let val = variant.to_possible_value().unwrap();
            width = val.get_name().len().max(width);
        }

        for variant in Self::value_variants() {
            let val = variant.to_possible_value().unwrap();

            write!(
                help,
                " {:>width$} - {}",
                val.get_name(),
                val.get_help().unwrap()
            )
            .unwrap();
            if let Some(rest) = Self::help_extended(val.get_name()) {
                let spacing = format!("\n{:width$}", "", width = width + 4);

                let rest = rest.replace('\n', &spacing);
                writeln!(help, "{spacing}{rest}").unwrap();
            } else {
                writeln!(help).unwrap();
            }
        }

        help
    }
}

#[derive(Debug, Clone, ValueEnum, PartialEq, Eq)]
pub enum DebugKey {
    /// Print the help message
    Help,
    /// Halt the compilation at a specified stage.
    Halt,
    /// Print the timings in a summary, of all stages of the compiler. `true` /
    /// `false` [default: false]
    Timings,
    /// Prints to the standard error, one or more of:
    Print,
}

impl ValueEnumExt for DebugKey {
    fn help() -> Self {
        Self::Help
    }

    fn name() -> &'static str {
        "Debug (-Z)"
    }

    fn help_extended(variant: &str) -> Option<&'static str> {
        match variant {
            "halt" => Some(
                "
Note that if you provide multiple halt kv, only the last will remain.

Stages:
* lexer
* parser
* dsir
* scir
* ssa
* codegen\
                ",
            ),
            "print" => Some(
                "\
* inputfile
* tokenstream
* ast
* dsir
* scir
* ssa
* asm\
                ",
            ),
            _ => None,
        }
    }
}

#[derive(Debug, Clone, ValueEnum, PartialEq, Eq)]
pub enum CodegenKey {
    /// Prints this help message
    Help,
    /// Optimization level `none`, `speed` and `speed_and_size` [default: none]
    OptLevel,
    /// Output the object file of the orb.`true` / `false` [default: false]
    OutputObj,
}

impl ValueEnumExt for CodegenKey {
    fn help() -> Self {
        Self::Help
    }

    fn name() -> &'static str {
        "Codegen"
    }

    fn help_extended(variant: &str) -> Option<&'static str> {
        _ = variant;

        None
    }
}

pub fn print_help_kvs<K: ValueEnumExt, V: FromStr>(kvs: &[Kv<K, V>]) -> bool {
    kvs.iter().any(|Kv { key, val: _ }| key.is_help())
}

/// Prints the target help message to stdout.
pub fn target_help() {
    println!(
        "\
Target format:

ARCHITECTURE-VENDOR-OPERATING_SYSTEM
ARCHITECTURE-VENDOR-OPERATING_SYSTEM-ENVIRONMENT

where for example:

- ARCHITECTURE = `x86_64`, `x86`, `arm`, `aarch64`, `riscv64`, `riscv32`
- VENDOR = `unknown`, `apple`, `pc`
- OPERATING_SYSTEM = `linux`, `windows`, `darwin`, `unknown`
- ENVIRONMENT = `gnu`, `msvc`, `android`

List of supported targets:\
"
    );

    for target in target::SUPPORTED_TARGETS {
        println!("{target}");
    }
}

/// Computed-args of lunc
#[derive(Debug)]
pub struct Argv {
    input: PathBuf,
    output: PathBuf,
    debug: DebugOptions,
    target: Triple,
    orb_name: String,
    color: ColorChoice,
    codegen: CodegenOptions,
}

impl Argv {
    pub fn dump_sink(&self, sink: &mut DiagnosticSink) {
        sink.emit_summary(&self.orb_name);
        let mut stream = StandardStream::stderr(self.color);

        sink.dump_with(&mut stream)
            .expect("failed to emit the diagnostics");
    }
}

/// Debug options
#[derive(Default, Debug)]
pub struct DebugOptions {
    halt: Option<CompStage>,
    timings: bool,
    print: Vec<InterRes>,
}

impl DebugOptions {
    pub fn print(&self, ir: InterRes) -> bool {
        self.print.contains(&ir)
    }

    pub fn halt(&self, stage: CompStage) -> bool {
        self.halt.as_ref().is_some_and(|s| *s == stage)
    }
}

/// Codegen options
#[derive(Debug)]
pub struct CodegenOptions {
    opt_level: OptLevel,
    output_obj: bool,
}

impl Default for CodegenOptions {
    fn default() -> Self {
        CodegenOptions {
            opt_level: OptLevel::None,
            output_obj: false,
        }
    }
}

/// Compilation stage
#[derive(Debug, Clone, ValueEnum, PartialEq, Eq)]
pub enum CompStage {
    Lexer,
    Parser,
    Dsir,
    Scir,
    Ssa,
    Codegen,
}

/// Intermediate result
#[derive(Debug, Clone, ValueEnum, PartialEq, Eq)]
pub enum InterRes {
    InputFile,
    TokenStream,
    Ast,
    Dsir,
    Scir,
    Ssa,
    Asm,
}

#[derive(Debug, Clone, Default)]
pub struct Timings {
    /// duration of setup:
    /// - reading the file to a String
    /// - creating the diagnostic sink
    /// - ..
    setup: Duration,
    /// duration of lexer
    lexer: Duration,
    /// duration of parser
    parser: Duration,
    /// duration of dsir
    dsir: Duration,
    /// duration of scir
    scir: Duration,
    /// duration of the ssa generation
    ssa: Duration,
    /// duration of the entire build
    total: Duration,
}

impl fmt::Display for Timings {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let Timings {
            setup,
            lexer,
            parser,
            dsir,
            scir,
            ssa,
            total,
        } = self.clone();

        writeln!(f, "Timings:")?;
        writeln!(f, "  setup: {}", humantime::format_duration(setup))?;
        writeln!(f, "  lexer: {}", humantime::format_duration(lexer))?;
        writeln!(f, " parser: {}", humantime::format_duration(parser))?;
        writeln!(f, "   dsir: {}", humantime::format_duration(dsir))?;
        writeln!(f, "   scir: {}", humantime::format_duration(scir))?;
        writeln!(f, "    ssa: {}", humantime::format_duration(ssa))?;
        writeln!(f, "= Total: {}", humantime::format_duration(total))?;

        Ok(())
    }
}

pub fn run() -> Result<()> {
    panic::set_hook(Box::new(|panic_info| {
        let thread = thread::current();
        let backtrace = Backtrace::capture();
        eprintln!("{}\n", panic_info);

        match backtrace.status() {
            BacktraceStatus::Captured => {
                if let Some(name) = thread.name() {
                    eprintln!("thread '{}'\n{}", name, backtrace);
                    eprintln!();
                } else {
                    eprintln!("{}", backtrace);
                    eprintln!();
                }
            }
            BacktraceStatus::Disabled => eprintln!(
                "note: run with `RUST_BACKTRACE=1` environment variable to display a backtrace"
            ),
            BacktraceStatus::Unsupported => eprintln!("note: backtrace is not supported."),
            status => {
                eprintln!("unknown backtrace status, {status:?}");
                abort()
            }
        }
        eprintln!("BUG: internal compiler error: unexpected panic.");
        eprintln!(
            "  = note: we would appreciate a bug report on https://github.com/lunprog/lun/issues/new",
        );
        eprintln!(
            "  = note: lunc {version} ({commit} {date})",
            version = env!("CARGO_PKG_VERSION"),
            commit = build::SHORT_COMMIT,
            date = &build::COMMIT_DATE[..10]
        );
    }));

    let raw_argv = RawLuncCli::try_parse()?;

    if raw_argv.version {
        eprintln!(
            "lunc {version} ({commit} {date})",
            version = env!("CARGO_PKG_VERSION"),
            commit = build::SHORT_COMMIT,
            date = &build::COMMIT_DATE[..10]
        );

        if raw_argv.verbose {
            eprintln!("host: {}", target::Triple::host());
            eprintln!("commit-hash: {}", build::COMMIT_HASH);
            eprintln!("commit-date: {}", build::COMMIT_DATE);
            eprintln!("rustc-version: {}", build::RUST_VERSION);
            eprintln!("rustc-toolchain: {}", build::RUST_CHANNEL);
        }

        return Ok(());
    }

    if print_help_kvs(&raw_argv.debug) {
        eprint!("{}", DebugKey::help_msg());

        return Ok(());
    }

    if print_help_kvs(&raw_argv.codegen) {
        eprint!("{}", CodegenKey::help_msg());

        return Ok(());
    }

    if let Some("help") = raw_argv.target.as_deref() {
        target_help();

        return Ok(());
    }

    let Some(input) = raw_argv.input else {
        return Err(CliError::NoInputFile);
    };

    let orb_name = raw_argv.orb_name.unwrap_or_else(|| {
        input
            .with_extension("")
            .file_name()
            .unwrap()
            .to_string_lossy()
            .to_string()
    });
    let output = raw_argv.output.unwrap_or(PathBuf::from(orb_name.as_str()));

    let target = if let Some(target_str) = raw_argv.target {
        Triple::from_str(&target_str)?
    } else {
        Triple::host()
    };

    let mut debug = DebugOptions::default();

    // here to know if we have defined multiple times one option
    let mut debug_halt_def = false;
    let mut debug_timings_def = false;

    for Kv { key, val } in raw_argv.debug {
        match key {
            DebugKey::Help => unreachable!(),
            DebugKey::Halt => {
                if debug_halt_def {
                    return Err(CliError::ArgumentUsedMultipleTimes("-Z halt".to_string()));
                }

                debug.halt = Some(
                    CompStage::from_str(&val, false).map_err(|_| CliError::InvalidHaltVal(val))?,
                );
                debug_halt_def = true;
            }
            DebugKey::Timings => {
                if debug_timings_def {
                    return Err(CliError::ArgumentUsedMultipleTimes(
                        "-Z timings".to_string(),
                    ));
                }

                debug.timings = val.parse().map_err(|_| CliError::InvalidTimingsVal(val))?;
                debug_timings_def = true;
            }
            DebugKey::Print => {
                debug.print.push(
                    InterRes::from_str(&val, false).map_err(|_| CliError::InvalidPrintVal(val))?,
                );
            }
        }
    }

    let mut codegen = CodegenOptions::default();

    // here to know if we have defined multiple times one option
    let mut codegen_optlevel_def = false;
    let mut codegen_outputobj_def = false;

    for Kv { key, val } in raw_argv.codegen {
        match key {
            CodegenKey::Help => unreachable!(),
            CodegenKey::OptLevel => {
                if codegen_optlevel_def {
                    return Err(CliError::ArgumentUsedMultipleTimes(
                        "-C opt-level".to_string(),
                    ));
                }

                codegen.opt_level = val.parse().map_err(|_| CliError::InvalidOptLevelVal(val))?;
                codegen_optlevel_def = true;
            }
            CodegenKey::OutputObj => {
                if codegen_outputobj_def {
                    return Err(CliError::ArgumentUsedMultipleTimes(
                        "-C output-obj".to_string(),
                    ));
                }

                codegen.output_obj = val
                    .parse()
                    .map_err(|_| CliError::InvalidOutputObjVal(val))?;
                codegen_outputobj_def = true;
            }
        }
    }

    let color = raw_argv.color.parse()?;

    let argv = Argv {
        input,
        output,
        debug,
        target,
        orb_name,
        color,
        codegen,
    };

    // ensure orb name can be an identifier
    if !is_identifier(&argv.orb_name) {
        return Err(CliError::NonIdentifierOrbName {
            orb_name: argv.orb_name.clone(),
        });
    }

    build_with_argv(argv)?;

    Ok(())
}

pub fn build_with_argv(argv: Argv) -> Result<()> {
    let mut timings = Timings::default();

    let top_instant = Instant::now();

    let opts = BuildOptions::new(&argv.orb_name, argv.target.clone());

    // 1. retrieve the source code, file => text
    let source_code = read_to_string(&argv.input).map_err(|err| CliError::FileIoError {
        path: argv.input.clone(),
        err,
    })?;

    //    maybe print source code
    if argv.debug.print(InterRes::InputFile) {
        eprintln!("{source_code}");
    }

    // 2. create the diagnostic sink
    let input_str = argv.input.clone().into_os_string().into_string().unwrap();
    let sink = DiagnosticSink::new();
    let root_fid = sink.register_file(input_str, source_code.clone());
    assert_eq!(root_fid, FileId::ROOT_MODULE);

    let builderr = || {
        let mut sink = sink.clone();
        argv.dump_sink(&mut sink);

        CliError::BuildDiagnostics {
            failed: sink.failed(),
        }
    };

    timings.setup = top_instant.elapsed();
    let lexer_instant = Instant::now();

    // 3. lexing, text => token stream
    let mut lexer = Lexer::new(sink.clone(), source_code.clone(), root_fid);
    let tokenstream = lexer.produce().ok_or_else(builderr)?;

    //    maybe print the token stream
    if argv.debug.print(InterRes::TokenStream) {
        eprint!("tokenstream = ");
        tokenstream.fmt(&mut stderr(), &source_code).unwrap();
    }
    if argv.debug.halt(CompStage::Lexer) {
        if sink.is_empty() {
            return Ok(());
        }

        Err(builderr())?;
    }

    timings.lexer = lexer_instant.elapsed();
    let parser_instant = Instant::now();

    // 4. parsing, token stream => AST
    let mut parser = Parser::new(tokenstream, sink.clone(), root_fid);
    let ast = parser.produce().ok_or_else(builderr)?;

    //    maybe print the ast
    if argv.debug.print(InterRes::Ast) {
        eprint!("ast = ");
        ast.dump();
        eprintln!();
    }
    if argv.debug.halt(CompStage::Parser) {
        if sink.is_empty() {
            return Ok(());
        }

        Err(builderr())?;
    }

    timings.parser = parser_instant.elapsed();
    let dsir_instant = Instant::now();

    // 5. desugarring, AST => DSIR
    let mut desugarrer = Desugarrer::new(sink.clone(), opts.orb_name());
    let dsir = desugarrer.produce(ast).ok_or_else(builderr)?;

    //    maybe print the DSIR
    if argv.debug.print(InterRes::Dsir) {
        eprint!("dsir = ");
        dsir.dump();
        eprintln!();
    }
    if argv.debug.halt(CompStage::Dsir) {
        if sink.is_empty() {
            return Ok(());
        }

        Err(builderr())?;
    }

    timings.dsir = dsir_instant.elapsed();
    let scir_instant = Instant::now();

    // 6. type-checking and all the semantic analysis, DSIR => SCIR
    let mut semacker = SemaChecker::new(sink.clone(), opts.clone());
    let scir = semacker.produce(dsir).ok_or_else(builderr)?;

    //    maybe print the SCIR
    if argv.debug.print(InterRes::Scir) {
        eprint!("scir = ");
        scir.dump();
        eprintln!();
    }
    if argv.debug.halt(CompStage::Scir) {
        if sink.is_empty() {
            return Ok(());
        }

        Err(builderr())?;
    }

    timings.scir = scir_instant.elapsed();
    let ssa_instant = Instant::now();

    // 7. generate the clif, SCIR => SSA (CLIF) => ASM at the same time.
    let cliftxt = argv.debug.print(InterRes::Ssa);
    let mut clifgen = ClifGen::new(opts.clone(), cliftxt, argv.codegen.opt_level);
    clifgen.produce(&mut ClifGenContext::default(), scir);

    //    maybe print the SSA
    if argv.debug.print(InterRes::Ssa) {
        eprintln!("; SSA of orb {}", opts.orb_name());
        eprint!("{}", clifgen.textrepr());
    }
    if argv.debug.halt(CompStage::Ssa) || argv.debug.halt(CompStage::Codegen) {
        // NOTE: we do not emit diags anymore.
        return Ok(());
    }

    if argv.codegen.output_obj {
        // write the object to file
        let obj = clifgen.finish_obj();
        let obj_bytes = obj.emit().unwrap();
        fs::write(argv.output.with_extension("o"), obj_bytes).unwrap();
    }

    timings.ssa = ssa_instant.elapsed();
    timings.total = top_instant.elapsed();

    if argv.debug.timings {
        eprint!("\n{timings}");
    }

    if sink.is_empty() {
        Ok(())
    } else {
        Err(builderr())
    }
}
