use std::{env, error::Error, path::Path};

use luntests::TestContext;
use termcolor::{ColorChoice, StandardStream};

const HELP_MESSAGE: &str = "\
Test suite for the Lun Compiler.

Usage: luntests [SUBCOMMAND]

Sub commands:
    record            Record the tests and make it the expected results
    help              Display this message
";

fn main() -> Result<(), Box<dyn Error>> {
    // TODO: remake using clap
    let mut args = env::args();
    _ = args.next(); // skip program name

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

    match args.next().as_deref() {
        Some("record") => record_tests(&mut tctx)?,
        Some("help") => eprint!("{HELP_MESSAGE}"),
        _ => run_tests(&mut tctx, &mut out)?,
    }

    Ok(())
}

fn record_tests(tctx: &mut TestContext) -> Result<(), Box<dyn Error>> {
    // TODO: be able to record only one test case
    tctx.record_tests()?;
    tctx.write_test_records()?;

    Ok(())
}

fn run_tests(tctx: &mut TestContext, out: &mut StandardStream) -> Result<(), Box<dyn Error>> {
    tctx.run_tests(out)?;
    Ok(())
}
