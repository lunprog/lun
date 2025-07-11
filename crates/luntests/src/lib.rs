use std::{
    error::Error,
    fmt,
    fs::{self, File},
    io::{Read, Write},
    path::{Path, PathBuf},
    process::{Command, Output},
    time::{Duration, Instant},
};

use indexmap::IndexMap;
use ron::ser::PrettyConfig;
use serde::{Deserialize, Serialize};
use termcolor::{Color, ColorSpec, StandardStream, WriteColor};

// TODO(URGENT): remove this any result and create an error type with thiserror
type AnyResult<T> = Result<T, Box<dyn std::error::Error>>;

#[derive(Debug, Clone, Copy)]
pub struct TestFailed;

impl Error for TestFailed {}

impl fmt::Display for TestFailed {
    fn fmt(&self, _: &mut fmt::Formatter<'_>) -> fmt::Result {
        Ok(())
    }
}

pub type Records = IndexMap<String, TestRecord>;

#[derive(Debug, Clone, PartialEq, Eq, Deserialize, Serialize)]
pub struct TestContext {
    /// expected outputs in the test, loaded from the `tests.ron` file
    records: Records,
    /// list of all the tests name found in the folder `tests/`
    tests: Vec<Test>,
}

impl TestContext {
    pub const TESTS_PATH: &str = "./tests.ron";

    pub fn new() -> TestContext {
        TestContext {
            records: IndexMap::new(),
            tests: Vec::new(),
        }
    }

    pub fn load_tests(&mut self, path: &Path) -> AnyResult<()> {
        if path.is_dir() {
            for entry in fs::read_dir(path)? {
                let entry = entry?;
                let entry_path = entry.path();

                if entry_path.is_dir() {
                    self.load_tests(&entry_path)?;
                } else {
                    let name = entry_path
                        .strip_prefix("./tests/")
                        .unwrap()
                        .with_extension("")
                        .to_string_lossy()
                        .to_string();

                    self.tests.push(Test {
                        name,
                        path: entry_path,
                    });
                }
            }
        }

        Ok(())
    }

    pub fn load_or_create_records(&mut self) -> AnyResult<()> {
        let mut file = File::open(Self::TESTS_PATH)?;

        let mut tests_str = String::new();
        file.read_to_string(&mut tests_str)?;

        let mut records = ron::from_str::<Records>(&tests_str).unwrap_or_else(|_| Records::new());

        // populate the missing tests
        for Test { name, path: _ } in &self.tests {
            if !records.contains_key(name) {
                records.insert(name.clone(), TestRecord::new());
            }
        }
        self.records = records;

        Ok(())
    }

    pub fn write_test_records(&mut self) -> AnyResult<()> {
        let mut file = File::create(TestContext::TESTS_PATH)?;

        // sort the keys so that the output order never changes
        self.records.sort_unstable_keys();

        let records_str = ron::ser::to_string_pretty(
            &self.records,
            PrettyConfig::default()
                .escape_strings(false)
                .depth_limit(80),
        )?;

        writeln!(file, "{records_str}")?;
        Ok(())
    }

    pub fn run_tests(&self, out: &mut StandardStream) -> AnyResult<()> {
        let start_test = Instant::now();

        let tests_count = self.tests.len();
        let mut summary = TestSummary {
            ok: 0,
            build_fail: 0,
            unexpected_build_out: 0,
            duration: Duration::ZERO,
            test_count: self.tests.len(),
        };

        for (n, Test { name, path }) in self.tests.iter().enumerate() {
            let test_record = self.records.get(name).unwrap();
            let mut cmd = Command::new("./target/debug/lunc");

            let extra_args = TestContext::compiler_args_from_name(name);
            cmd.args(extra_args);

            cmd.arg(path);

            write!(out, "[{}/{tests_count}] testing '{name}' ... ", n + 1)?;
            // force flushing so that we can see the progress of the tests
            out.flush()?;

            let cmd_output = cmd.output()?;
            let compiler_out = String::from_utf8_lossy(&cmd_output.stderr).to_string();

            if !cmd_output.status.success() {
                // compiler failed to build the test
                out.set_color(&TestContext::compiler_fail_color_spec())?;
                writeln!(out, "BUILD FAILED")?;
                summary.build_fail += 1;
                out.reset()?;

                TestContext::log_test_compiler_fail(out, &cmd_output)?;
                continue;
            }

            if compiler_out != test_record.expected_compiler_out {
                // compiler outputed something different than what was expected
                out.set_color(&TestContext::compiler_fail_color_spec())?;
                writeln!(out, "UNEXPECTED BUILD OUT")?;
                summary.unexpected_build_out += 1;
                out.reset()?;

                TestContext::log_test_compiler_fail(out, &cmd_output)?;
                continue;
            }

            // TODO: implement test running
            out.set_color(&TestContext::ok_color_spec())?;
            writeln!(out, "OK")?;
            summary.ok += 1;
            out.reset()?;

            // force flushing so that we can see the progress of the tests
            out.flush()?;
        }

        summary.duration = start_test.elapsed();
        summary.write_report(out)?;

        if summary.failed() {
            return Err(Box::new(TestFailed));
        }

        Ok(())
    }

    pub fn record_tests(&mut self) -> AnyResult<()> {
        for Test { name, path } in &self.tests {
            let test_record = self.records.get_mut(name).unwrap();
            let mut cmd = Command::new("./target/debug/lunc");

            let extra_args = TestContext::compiler_args_from_name(name);
            cmd.args(extra_args);

            cmd.arg(path);

            let cmd_output = cmd.output()?;
            let compiler_out = String::from_utf8_lossy(&cmd_output.stderr).to_string();

            test_record.expected_compiler_out = compiler_out;
            // TODO: implement test running
        }

        Ok(())
    }

    pub fn compiler_fail_color_spec() -> ColorSpec {
        let mut color_spec = ColorSpec::new();
        color_spec.set_fg(Some(Color::Red)).set_intense(true);
        color_spec
    }

    pub fn ok_color_spec() -> ColorSpec {
        let mut color_spec = ColorSpec::new();
        color_spec.set_fg(Some(Color::Green)).set_intense(true);
        color_spec
    }

    fn compiler_args_from_name(name: &str) -> &[&str] {
        match name {
            _ if name.starts_with("lexer/") => &["-Dhalt-at=lexer", "-Dprint=tokenstream"],
            _ => &[],
        }
    }

    fn log_test_compiler_fail(out: &mut StandardStream, cmd_output: &Output) -> AnyResult<()> {
        writeln!(out, "\nstderr:")?;

        out.write_all(&cmd_output.stderr)?;

        writeln!(out, "\nexit code: {}", cmd_output.status.code().unwrap())?;
        Ok(())
    }
}

impl Default for TestContext {
    fn default() -> Self {
        TestContext::new()
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Deserialize, Serialize)]
pub struct Test {
    name: String,
    path: PathBuf,
}

#[derive(Debug, Clone, PartialEq, Eq, Deserialize, Serialize)]
pub struct TestRecord {
    expected_compiler_out: String,
    expected_test_out: String,
}

impl TestRecord {
    pub fn new() -> TestRecord {
        TestRecord {
            expected_compiler_out: String::new(),
            expected_test_out: String::new(),
        }
    }
}

impl Default for TestRecord {
    fn default() -> Self {
        TestRecord::new()
    }
}

#[derive(Debug, Clone)]
pub struct TestSummary {
    ok: usize,
    build_fail: usize,
    unexpected_build_out: usize,
    // other things..
    duration: Duration,
    test_count: usize,
}

impl TestSummary {
    pub fn failed(&self) -> bool {
        let TestSummary {
            ok: _,
            build_fail,
            unexpected_build_out,
            duration: _,
            test_count: _,
        } = self;

        *build_fail != 0 || *unexpected_build_out != 0
    }

    pub fn write_report(&self, out: &mut StandardStream) -> AnyResult<()> {
        writeln!(out)?;
        out.set_color(ColorSpec::new().set_bold(true))?;

        let duration_str = humantime::format_duration(self.duration);

        if self.failed() {
            out.set_color(&TestContext::compiler_fail_color_spec())?;
            write!(out, "Tests failed ({duration_str})")?;
            out.reset()?;

            writeln!(out, ", {}/{} passed successfully", self.ok, self.test_count)?;
            writeln!(
                out,
                "{} failed to build and {} had an unexpected compiler output",
                self.build_fail, self.unexpected_build_out
            )?;
        } else {
            writeln!(
                out,
                "Tests succeeded, {} passed successfully in {duration_str}",
                self.ok,
            )?;
        }
        out.reset()?;

        Ok(())
    }
}
