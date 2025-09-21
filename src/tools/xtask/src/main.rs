use std::{
    fs,
    path::{Path, PathBuf},
    process::{Command, ExitCode, ExitStatus},
};

use clap::{Parser, Subcommand};

#[derive(Debug, Clone, Parser)]
pub struct Cli {
    #[command(subcommand)]
    cmd: Cmd,
}

#[derive(Debug, Clone, Subcommand)]
pub enum Cmd {
    /// Runs the compiler with the given arguments, rebuild it quietly if needed
    Lunc {
        /// arguments to pass to 'lunc'
        #[arg(last = true)]
        args: Vec<String>,
    },
    /// Runs the compiler tests and forwards it the following arguments
    Test {
        /// arguments to pass to 'luntests'
        #[arg(last = true)]
        args: Vec<String>,
    },
    /// Watch for changes in source code and runs cmd if provided or defaults to
    /// `cargo check`
    Watch {
        /// arguments to pass to 'cargo watch'
        #[arg(last = true)]
        args: Vec<String>,
    },
    /// Compile the examples and return the return code of lunc if it failed.
    Examples,
    /// Returns the number of line of codes in the `tests` folder
    Loc,
}

pub fn build(quiet: bool, bin: &str) -> ExitStatus {
    let mut args = vec!["build", "--bin", bin];

    if quiet {
        args.push("--quiet");
    }

    let mut cmd = Command::new("cargo");
    cmd.args(args);

    cmd.status()
        .unwrap_or_else(|e| panic!("failed to build {bin}: {e}"))
}

fn main() -> ExitCode {
    let args = Cli::parse();

    match args.cmd {
        Cmd::Lunc { args } => {
            // build the compiler
            let build_status = build(true, "lunc");

            if !build_status.success() {
                return ExitCode::FAILURE;
            }

            // run the compiler
            let mut cmd = Command::new("target/debug/lunc");
            cmd.args(args);

            let lunc_status = cmd.status().expect("failed to run lunc");

            if !lunc_status.success() {
                return ExitCode::FAILURE;
            }

            ExitCode::SUCCESS
        }
        Cmd::Test { args } => {
            // build the compiler
            let build_status = build(true, "lunc");

            if !build_status.success() {
                return ExitCode::FAILURE;
            }

            // build the test suite
            let build_status = build(true, "luntests");

            if !build_status.success() {
                return ExitCode::FAILURE;
            }

            // run the tests
            let mut cmd = Command::new("target/debug/luntests");
            cmd.args(args);

            let luntests_status = cmd.status().expect("failed to run luntests");

            if !luntests_status.success() {
                return ExitCode::FAILURE;
            }

            ExitCode::SUCCESS
        }
        Cmd::Watch { args } => {
            // start watching
            let mut cmd = Command::new("cargo");
            cmd.arg("watch");
            if !args.is_empty() {
                cmd.args(args);
            }

            let watch_status = cmd.status().expect("failed to run luntests");

            if !watch_status.success() {
                return ExitCode::FAILURE;
            }

            ExitCode::SUCCESS
        }
        Cmd::Examples => {
            // collect the examples
            let mut examples = Vec::new();

            fn walk_dir(dir: &Path, examples: &mut Vec<PathBuf>) {
                if let Ok(entries) = fs::read_dir(dir) {
                    for entry in entries.flatten() {
                        let path = entry.path();
                        if path.is_dir() {
                            // we only add the files at the root of the examples
                            // folder because we might add examples with
                            // multiple files in a separate dir
                        } else {
                            examples.push(path);
                        }
                    }
                }
            }

            walk_dir(Path::new("examples"), &mut examples);

            // build the compiler
            let build_status = build(true, "lunc");

            if !build_status.success() {
                return ExitCode::FAILURE;
            }

            // try to build the examples
            for example in examples {
                eprintln!("Try to build {}..", example.display());
                let mut cmd = Command::new("target/debug/lunc");

                cmd.arg(example);
                cmd.arg("-Zhalt=scir"); // TODO: remove this when clif gen will be fully implemented

                let lunc_status = cmd.status().expect("failed to run lunc");

                if !lunc_status.success() {
                    eprintln!("    FAILED");
                    return ExitCode::FAILURE;
                }
                eprintln!("    SUCCESS");
            }

            // try to build the hello_c_ffi example
            eprintln!("Try to build hello_c_ffi..");
            let mut cmd = Command::new("make");
            cmd.current_dir("examples/hello_c_ffi");
            cmd.arg("run");
            let lunc_status = cmd.status().expect("failed to run lunc");

            if !lunc_status.success() {
                eprintln!("    FAILED");
                return ExitCode::FAILURE;
            }
            eprintln!("    SUCCESS");

            ExitCode::SUCCESS
        }
        Cmd::Loc => {
            // start watching

            fn walk_dir(dir: &Path) -> usize {
                let mut loc = 0;

                if let Ok(entries) = fs::read_dir(dir) {
                    for entry in entries.flatten() {
                        let path = entry.path();
                        if path.is_dir() {
                            loc += walk_dir(&path);
                        } else {
                            let lines = {
                                let content =
                                    fs::read_to_string(&path).expect("failed to read a file");
                                content.lines().count()
                            };

                            eprintln!("{:>8} {}", lines, path.display());
                            loc += lines;
                        }
                    }
                }

                loc
            }

            eprintln!("{:>8} total", walk_dir(Path::new("tests")));

            ExitCode::SUCCESS
        }
    }
}
