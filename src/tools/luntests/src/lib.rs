#![doc(
    html_logo_url = "https://raw.githubusercontent.com/lunprog/lun/main/src/assets/logo_no_bg_black.png"
)]

use std::{
    convert::Infallible,
    fs::{self, File},
    io::{self, Read, Write},
    path::{Path, PathBuf},
    process::{Command, Output},
    str::FromStr,
    time::{Duration, Instant},
};

use indexmap::IndexMap;
use lunc_utils::fast_digit_length;
use ron::ser::PrettyConfig;
use serde::{Deserialize, Serialize};
use termcolor::{Color, ColorSpec, StandardStream, WriteColor};
use thiserror::Error;

#[derive(Debug, Error)]
pub enum TestError {
    #[error(transparent)]
    Io(#[from] io::Error),
    #[error(transparent)]
    Ron(#[from] ron::Error),
    #[error("failed to run the test")]
    Failed,
}

pub type Records = IndexMap<String, TestRecord>;

#[derive(Debug, Clone, PartialEq, Eq)]
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

    pub fn load_tests(&mut self, path: &Path) -> Result<(), TestError> {
        assert!(path.is_dir());

        let tests_entries = fs::read_dir(path)?;

        for tests_entry in tests_entries.flatten() {
            let stage_path = tests_entry.path();

            let stage_entries = fs::read_dir(stage_path)?;
            for stage_entry in stage_entries.flatten() {
                let test_path = stage_entry.path();
                if test_path.is_dir() {
                    continue;
                }

                if test_path.starts_with("./tests/multifile/") {
                    // NOTE: we are not really skipping this test, we just add
                    // him after but just the `multifile/lib` one
                    continue;
                }

                let name = test_path
                    .strip_prefix("./tests/")
                    .unwrap()
                    .with_extension("")
                    .to_string_lossy()
                    .to_string();
                let Ok(stage) = TestStage::from_str(&name);

                self.tests.push(Test {
                    name,
                    path: test_path,
                    stage,
                });
            }
        }

        self.tests.push(Test {
            name: String::from("multifile/lib"),
            path: PathBuf::from("./tests/multifile/lib.lun"),
            stage: TestStage::Multifile,
        });

        self.tests.sort_by(|a, b| a.name.cmp(&b.name));

        Ok(())
    }

    pub fn load_or_create_records(&mut self) -> Result<(), TestError> {
        let mut file = File::open(Self::TESTS_PATH)?;

        let mut tests_str = String::new();
        file.read_to_string(&mut tests_str)?;

        let mut records = ron::from_str::<Records>(&tests_str).unwrap_or_else(|_| Records::new());

        // populate the missing tests
        for Test {
            name,
            path: _,
            stage: _,
        } in &self.tests
        {
            if !records.contains_key(name) {
                records.insert(name.clone(), TestRecord::new());
            }
        }
        self.records = records;

        Ok(())
    }

    pub fn write_test_records(&mut self) -> Result<(), TestError> {
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

    pub fn run_tests(&self, out: &mut StandardStream) -> Result<(), TestError> {
        let start_test = Instant::now();

        let tests_count = self.tests.len();
        let width = fast_digit_length::<10>(tests_count as u128) as usize;

        let mut summary = TestSummary {
            ok: 0,
            build_fail: 0,
            unexpected_build_out: 0,
            duration: Duration::ZERO,
            test_count: self.tests.len(),
        };

        for (n, Test { name, path, stage }) in self.tests.iter().enumerate() {
            let test_record = self.records.get(name).unwrap();
            let mut cmd = Command::new("./target/debug/lunc");

            let extra_args = stage.to_compiler_args();
            cmd.args(extra_args);

            cmd.args(["--color", "never"]);
            cmd.arg(path);

            write!(
                out,
                "[{1:>00$}/{tests_count}] testing '{name}' ... ",
                width,
                n + 1
            )?;
            // force flushing so that we can see the progress of the tests
            out.flush()?;

            let cmd_output = cmd.output()?;
            let compiler_out = String::from_utf8_lossy(&cmd_output.stderr).to_string();

            if cmd_output.status.code().unwrap() as u8 != test_record.compiler_code {
                // compiler failed to build the test
                out.set_color(&TestContext::compiler_fail_color_spec())?;
                writeln!(out, "BUILD FAILED")?;
                summary.build_fail += 1;
                out.reset()?;

                TestContext::log_test_compiler_fail(out, &cmd_output)?;
                continue;
            }

            if compiler_out != test_record.compiler_out {
                // compiler outputted something different than what was expected
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
            return Err(TestError::Failed);
        }

        Ok(())
    }

    pub fn record_tests(&mut self, out: &mut StandardStream) -> Result<(), TestError> {
        for Test { name, path, stage } in &self.tests {
            let test_record = self.records.get_mut(name).unwrap();
            let mut cmd = Command::new("./target/debug/lunc");

            let extra_args = stage.to_compiler_args();
            cmd.args(extra_args);

            cmd.args(["--color", "never"]);

            cmd.arg(path);

            let cmd_output = cmd.output()?;
            let compiler_out = String::from_utf8_lossy(&cmd_output.stderr).to_string();

            test_record.compiler_out = compiler_out;
            let old_compcode = test_record.compiler_code;
            test_record.compiler_code = cmd_output.status.code().unwrap() as u8;

            if old_compcode != test_record.compiler_code {
                out.set_color(&TestContext::compiler_fail_color_spec())?;
                write!(out, "NOTE: ")?;
                out.reset()?;
                writeln!(
                    out,
                    "test {}, compiler code {old_compcode} -> {}",
                    name, test_record.compiler_code
                )?;
            }

            if test_record.compiler_code == 101 {
                out.set_color(&TestContext::compiler_fail_color_spec())?;
                write!(out, "FATAL: ")?;
                out.reset()?;
                writeln!(out, "test {}, has code 101, it is an ICE", name)?;
                writeln!(out)?;
            }

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

    fn log_test_compiler_fail(
        out: &mut StandardStream,
        cmd_output: &Output,
    ) -> Result<(), TestError> {
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

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Test {
    name: String,
    path: PathBuf,
    stage: TestStage,
}

/// At which stage the compiler should stop
#[derive(Debug, Clone, PartialEq, Eq, Deserialize, Serialize)]
pub enum TestStage {
    /// the compiler should not stop, and so run the test
    None,
    Lexer,
    Parser,
    Dsir,
    Scir,
    Behavior,
    Multifile,
}

impl TestStage {
    pub fn to_compiler_args(&self) -> &[&str] {
        match self {
            TestStage::None => &[],
            TestStage::Lexer => &["-Zhalt=lexer", "-Zprint=token-stream"],
            TestStage::Parser => &["-Zhalt=parser", "-Zprint=ast"],
            TestStage::Dsir => &["-Zhalt=dsir", "-Zprint=dsir"],
            TestStage::Scir => &["-Zhalt=scir", "-Zprint=scir", "--orb-type", "llib"],
            TestStage::Behavior => &["-Zprint=ssa", "-Zprint=scir"],
            TestStage::Multifile => &[
                "-Zprint=scir",
                "-Zhalt=scir", // remove after cranelift gen is fully implemented
                "--orb-name",
                "multifile",
            ],
        }
    }
}

impl FromStr for TestStage {
    type Err = Infallible;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        if s.starts_with("lexer/") {
            Ok(TestStage::Lexer)
        } else if s.starts_with("parser/") {
            Ok(TestStage::Parser)
        } else if s.starts_with("desugaring/") {
            Ok(TestStage::Dsir)
        } else if s.starts_with("scir/") {
            Ok(TestStage::Scir)
        } else if s.starts_with("behavior/") {
            Ok(TestStage::Behavior)
        } else {
            Ok(TestStage::None)
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Deserialize, Serialize)]
pub struct TestRecord {
    /// compiler stderr output
    compiler_out: String,
    /// compiler process exit code
    compiler_code: u8,
    /// test stdout output
    test_out: String,
    /// test process exit code
    test_code: u8,
}

impl TestRecord {
    pub fn new() -> TestRecord {
        TestRecord {
            compiler_out: String::new(),
            compiler_code: 0,
            test_out: String::new(),
            test_code: 0,
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

    pub fn write_report(&self, out: &mut StandardStream) -> Result<(), TestError> {
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
