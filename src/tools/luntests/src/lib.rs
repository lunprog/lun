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
    pub const BUILD_TESTS_PATH: &str = "./build/tests";

    pub fn new() -> TestContext {
        TestContext {
            records: IndexMap::new(),
            tests: Vec::new(),
        }
    }

    pub fn create_build_tests_dir() -> Result<(), TestError> {
        fs::create_dir_all(Self::BUILD_TESTS_PATH)?;

        Ok(())
    }

    pub fn load_tests(&mut self, path: &Path) -> Result<(), TestError> {
        assert!(path.is_dir());

        let tests_entries = fs::read_dir(path)?;

        for tests_entry in tests_entries.flatten() {
            let stage_path = tests_entry.path();

            if stage_path.starts_with("./tests/README.md") {
                // NOTE: it's just README.md and not a test so we just
                // skip it.
                continue;
            }

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

                if stage == TestStage::Scir || stage == TestStage::Behavior {
                    continue;
                }

                self.tests.push(Test {
                    name,
                    path: test_path,
                    stage,
                });
            }
        }

        // self.tests.push(Test {
        //     name: String::from("multifile/lib"),
        //     path: PathBuf::from("./tests/multifile/lib.lun"),
        //     stage: TestStage::Multifile,
        // });

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

        Self::create_build_tests_dir()?;

        let mut summary = TestSummary {
            ok: 0,
            fail: 0,
            unexpected_out: 0,
            duration: Duration::ZERO,
            test_count: self.tests.len(),
        };

        for (n, Test { name, path, stage }) in self.tests.iter().enumerate() {
            let test_record = self.records.get(name).unwrap();
            let mut cmd = Command::new("./target/debug/lunc");

            let bin_path = format!(
                "{}/{}",
                Self::BUILD_TESTS_PATH,
                name.split('/').nth(1).unwrap()
            );

            let extra_args = stage.to_compiler_args();
            cmd.args(extra_args)
                .args(["--color", "never"])
                .arg("-o")
                .arg(&bin_path)
                .arg(path);

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

            let compiler_code = cmd_output.status.code().unwrap() as u8;
            if compiler_code != test_record.compiler_code {
                // compiler failed to build the test
                out.set_color(&TestContext::compiler_fail_color_spec())?;
                writeln!(out, "BUILD FAILED")?;
                summary.fail += 1;
                out.reset()?;

                TestContext::log_test_compiler_fail("compiler", out, &cmd_output, true)?;
                continue;
            }

            let mut build_fail = false;

            if compiler_out != test_record.compiler_out {
                // compiler outputted something different than what was expected
                out.set_color(&TestContext::compiler_fail_color_spec())?;
                writeln!(out, "UNEXPECTED BUILD OUT")?;
                summary.unexpected_out += 1;
                out.reset()?;

                TestContext::log_test_compiler_fail("compiler", out, &cmd_output, true)?;
                build_fail = true;
            }

            // run test if stage says so and the EXPECTED compiler code is zero
            if stage.run_test() && test_record.compiler_code == 0 {
                cmd = Command::new(&bin_path);

                let test_output = cmd.output()?;
                let test_out = String::from_utf8_lossy(&test_output.stdout).to_string();

                if test_output.status.code().unwrap() as u8 != test_record.test_code {
                    // test failed
                    if !build_fail {
                        out.set_color(&TestContext::compiler_fail_color_spec())?;
                        writeln!(out, "TEST FAILED")?;
                        summary.fail += 1;
                        out.reset()?;
                    }

                    TestContext::log_test_compiler_fail("test", out, &test_output, false)?;
                    continue;
                }

                if test_out != test_record.test_out {
                    // test outputted something different than what was expected
                    if !build_fail {
                        out.set_color(&TestContext::compiler_fail_color_spec())?;
                        writeln!(out, "UNEXPECTED TEST OUT")?;
                        summary.unexpected_out += 1;
                        out.reset()?;
                    }

                    TestContext::log_test_compiler_fail("test", out, &test_output, false)?;
                    continue;
                }
            }

            if build_fail {
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
        Self::create_build_tests_dir()?;

        for Test { name, path, stage } in &self.tests {
            let test_record = self.records.get_mut(name).unwrap();
            let mut cmd = Command::new("./target/debug/lunc");

            let bin_path = format!(
                "{}/{}",
                Self::BUILD_TESTS_PATH,
                name.split('/').nth(1).unwrap()
            );

            let extra_args = stage.to_compiler_args();
            cmd.args(extra_args)
                .args(["--color", "never"])
                .arg("-o")
                .arg(&bin_path)
                .arg(path);

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

            if stage.run_test() && test_record.compiler_code == 0 {
                cmd = Command::new(&bin_path);

                let test_output = cmd.output().unwrap();
                let test_out = String::from_utf8_lossy(&test_output.stdout).to_string();

                test_record.test_out = test_out;
                let old_testcode = test_record.test_code;
                test_record.test_code = test_output.status.code().unwrap() as u8;

                if old_testcode != test_record.test_code {
                    out.set_color(&TestContext::compiler_fail_color_spec())?;
                    write!(out, "NOTE: ")?;
                    out.reset()?;
                    writeln!(
                        out,
                        "test {}, test code {old_testcode} -> {}",
                        name, test_record.test_code
                    )?;
                }
            }
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
        name: &'static str,
        out: &mut StandardStream,
        cmd_output: &Output,
        stderr: bool,
    ) -> Result<(), TestError> {
        if stderr {
            writeln!(out, "\nstderr({name}):")?;
            out.write_all(&cmd_output.stderr)?;
        } else {
            writeln!(out, "\nstdout({name}):")?;
            out.write_all(&cmd_output.stdout)?;
        }

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
    Utir,
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
            TestStage::Utir => &["-Zhalt=utir", "-Zprint=utir"],
            // TestStage::Scir => &["-Zhalt=scir", "-Zprint=scir", "--orb-type", "llib"],
            // TestStage::Behavior => &["-Zprint=ssa", "-Zprint=scir"],
            TestStage::Scir | TestStage::Behavior => &[],
            TestStage::Multifile => &[
                "-Zprint=scir",
                "-Zhalt=scir", // remove after cranelift gen is fully implemented
                "--orb-name",
                "multifile",
            ],
        }
    }

    pub fn run_test(&self) -> bool {
        matches!(self, Self::Behavior)
    }
}

impl FromStr for TestStage {
    type Err = Infallible;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        if s.starts_with("lexer/") {
            Ok(TestStage::Lexer)
        } else if s.starts_with("parser/") {
            Ok(TestStage::Parser)
        } else if s.starts_with("dsir/") {
            Ok(TestStage::Dsir)
        } else if s.starts_with("utir/") {
            Ok(TestStage::Utir)
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
    fail: usize,
    unexpected_out: usize,
    // other things..
    duration: Duration,
    test_count: usize,
}

impl TestSummary {
    pub fn failed(&self) -> bool {
        let TestSummary {
            ok: _,
            fail,
            unexpected_out,
            duration: _,
            test_count: _,
        } = self;

        *fail != 0 || *unexpected_out != 0
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
                "{} failed to build/test and {} had an unexpected compiler/test output",
                self.fail, self.unexpected_out
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
