use std::{env, path::Path, process};

use luntests::{TestContext, TestError};
use termcolor::{ColorChoice, StandardStream};

use clap::{Parser, Subcommand};

#[derive(Debug, Clone, Parser)]
pub struct Cli {
    #[command(subcommand)]
    cmd: Option<Cmd>,
}

#[derive(Debug, Clone, Subcommand)]
pub enum Cmd {
    /// Record tests and make the output the expected output
    Record,
}

fn main() -> Result<(), TestError> {
    let args = Cli::parse();

    let workspace_path = Path::new(".");
    let tests_path = workspace_path.join("tests");
    let mut out = StandardStream::stderr(
        env::var("LUNTESTS_COLOR")
            .map(|c| c.parse().expect("failed to parse color choice"))
            .unwrap_or(ColorChoice::Auto),
    );

    let mut tctx = TestContext::new();
    tctx.load_tests(&tests_path)?;
    tctx.load_or_create_records()?;

    match args.cmd {
        Some(Cmd::Record) => record_tests(&mut tctx)?,
        None => match run_tests(&mut tctx, &mut out) {
            Ok(()) => {}
            Err(()) => process::exit(1),
        },
    }

    Ok(())
}

fn record_tests(tctx: &mut TestContext) -> Result<(), TestError> {
    // TODO: be able to record only one test case
    tctx.record_tests()?;
    tctx.write_test_records()?;

    Ok(())
}

fn run_tests(tctx: &mut TestContext, out: &mut StandardStream) -> Result<(), ()> {
    let res = tctx.run_tests(out);
    match res {
        Ok(()) => Ok(()),
        Err(TestError::Failed) => Err(()),
        Err(e) => {
            eprintln!("ERROR: {e}");
            Err(())
        }
    }
}
