use std::{
    fs,
    path::Path,
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
