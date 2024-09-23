use assert_cmd::prelude::*;
use std::{
    env,
    error::Error,
    fs::File,
    io::{BufRead, BufReader, Write},
    path::{Path, PathBuf},
    process::Command,
};

use similar::{ChangeTag, TextDiff};

use termcolor::*;

fn main() {
    // Build `creusot-rustc` and `cargo-creusot`

    let creusot_rustc = escargot::CargoBuild::new()
        .bin("creusot-rustc")
        .current_release()
        .manifest_path("../creusot-rustc/Cargo.toml")
        .current_target()
        .run()
        .unwrap();

    let cargo_creusot = escargot::CargoBuild::new()
        .bin("cargo-creusot")
        .current_release()
        .manifest_path("../cargo-creusot/Cargo.toml")
        .current_target()
        .run()
        .unwrap()
        .command();

    let mut base_path = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    base_path.pop();

    let mut temp_file = base_path.clone();
    temp_file.push("target");
    temp_file.push("debug");
    temp_file.push("libcreusot_contracts.cmeta");

    let mut metadata_file = cargo_creusot;
    metadata_file.current_dir(base_path);
    metadata_file.arg("creusot").args(&[
        "--metadata-path".as_ref(),
        temp_file.as_os_str(),
        "--output-file=/dev/null".as_ref(),
    ]);
    metadata_file.args(&["--", "--package", "creusot-contracts"]).env("CREUSOT_CONTINUE", "true");

    if !metadata_file.status().expect("could not dump metadata for `creusot_contracts`").success() {
        // eprintln!("{}", String::from_utf8_lossy(&metadata_file.output().unwrap().stderr));
        std::process::exit(1);
    }

    should_fail("tests/should_fail/**/*.rs", |p| {
        run_creusot(creusot_rustc.path(), p, &temp_file.to_string_lossy())
    });
    should_succeed("tests/should_succeed/**/*.rs", |p| {
        run_creusot(creusot_rustc.path(), p, &temp_file.to_string_lossy())
    });
}

fn run_creusot(
    creusot_rustc: &Path,
    file: &Path,
    contracts: &str,
) -> Option<std::process::Command> {
    let header_line = BufReader::new(File::open(&file).unwrap()).lines().nth(0).unwrap().unwrap();
    if header_line.contains("UISKIP") {
        return None;
    }

    let mut cmd = Command::new(creusot_rustc);
    cmd.current_dir(file.parent().unwrap());
    let mut base_path = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    base_path.pop();
    base_path.push("target");
    base_path.push("debug");

    let config_paths = creusot_dev_config::paths().unwrap();

    let creusot_contract_path = base_path.join("libcreusot_contracts.rlib");
    let creusot_contract_path =
        creusot_contract_path.to_str().expect("invalid utf-8 in contract path");
    let creusot_contract_path = normalize_file_path(creusot_contract_path);

    // Magic comment with instructions for creusot
    let header_line = BufReader::new(File::open(file).unwrap()).lines().nth(0).unwrap().unwrap();
    // Find comment chunks of the form CREUSOT_ARG=ARGUMENT. Does not support spaces in arguments currently (would require real parser)
    let args: Vec<_> = header_line
        .split(" ")
        .filter_map(|chunk| {
            let (first, rest) = chunk.split_once("=")?;
            if first != "CREUSOT_ARG" {
                None
            } else {
                Some(rest)
            }
        })
        .collect();

    cmd.args(&[
        "--stdout",
        "--export-metadata=false",
        "--span-mode=relative",
        // we will write the coma output next to the .rs file
        "--spans-relative-to=.",
    ]);
    cmd.args(args);
    cmd.args(&[
        "--creusot-extern",
        &format!("creusot_contracts={}", normalize_file_path(contracts)),
    ]);
    cmd.arg("--why3-path").arg(&config_paths.why3);
    cmd.arg("--why3-config-file").arg(&config_paths.why3_config);

    cmd.args(&["--", "-Zno-codegen", "--crate-type=lib"]);
    cmd.args(&["--extern", &format!("creusot_contracts={}", creusot_contract_path)]);

    let mut dep_path = base_path;
    dep_path.push("deps");
    cmd.arg(format!("-Ldependency={}/", dep_path.display()));
    cmd.arg(file.file_name().unwrap());
    Some(cmd)
}

fn should_succeed<B>(s: &str, b: B)
where
    B: Fn(&Path) -> Option<std::process::Command>,
{
    glob_runner(s, b, true);
}

fn should_fail<B>(s: &str, b: B)
where
    B: Fn(&Path) -> Option<std::process::Command>,
{
    glob_runner(s, b, false);
}

fn glob_runner<B>(s: &str, command_builder: B, should_succeed: bool)
where
    B: Fn(&Path) -> Option<std::process::Command>,
{
    let mut out = StandardStream::stdout(ColorChoice::Always);

    let mut test_count = 0;
    let mut test_failures = 0;
    let bless = std::env::args().any(|arg| arg == "--bless");
    let filter = std::env::args().nth(1);

    for entry in glob::glob(s).expect("Failed to read glob pattern") {
        test_count += 1;
        let entry = entry.unwrap();

        if let Some(ref filter) = filter {
            if !entry.to_str().map(|entry| entry.contains(filter)).unwrap_or(false) {
                continue;
            }
        }
        let output = match command_builder(&entry) {
            None => continue,
            Some(mut c) => c.output().unwrap(),
        };

        let stderr = entry.with_extension("stderr");
        let stdout = entry.with_extension("coma");

        write!(&mut out, "Testing {} ... ", entry.display()).unwrap();

        if bless {
            out.set_color(ColorSpec::new().set_fg(Some(Color::Blue))).unwrap();
            writeln!(&mut out, "blessed").unwrap();
            out.reset().unwrap();
            let (success, _) = differ(output.clone(), &stdout, &stderr, should_succeed).unwrap();

            if !success {
                out.set_color(ColorSpec::new().set_fg(Some(Color::Red))).unwrap();
                writeln!(&mut out, "failure").unwrap();
                out.reset().unwrap();
            }

            if output.stdout.is_empty() {
                let _ = std::fs::remove_file(stdout);
            } else {
                std::fs::write(stdout, &output.stdout).unwrap();
            }

            if output.stderr.is_empty() {
                let _ = std::fs::remove_file(stderr);
            } else {
                std::fs::write(stderr, &output.stderr).unwrap();
            }
        } else {
            let (success, mut buf) =
                differ(output.clone(), &stdout, &stderr, should_succeed).unwrap();

            if success {
                out.set_color(ColorSpec::new().set_fg(Some(Color::Green))).unwrap();
                writeln!(&mut out, "ok").unwrap();
            } else {
                out.set_color(ColorSpec::new().set_fg(Some(Color::Red))).unwrap();
                writeln!(&mut out, "failure").unwrap();

                test_failures += 1;
            };
            out.reset().unwrap();

            buf.reset().unwrap();
            let wrt = BufferWriter::stdout(ColorChoice::Always);
            wrt.print(&buf).unwrap();
        }
    }

    if test_failures > 0 {
        out.set_color(ColorSpec::new().set_fg(Some(Color::Red))).unwrap();
        drop(out);
        panic!("{} failures out of {} tests", test_failures, test_count);
    }
}

fn compare_str(buf: &mut Buffer, got: &str, expect: &str) -> bool {
    use similar::Algorithm;
    use std::time::Duration;

    if got == expect {
        return true;
    }

    let got = normalize_spans(&normalize_newlines(got));
    let expect = normalize_spans(&normalize_newlines(expect));

    let result = TextDiff::configure()
        .newline_terminated(false)
        .timeout(Duration::from_millis(200))
        .algorithm(Algorithm::Patience)
        .diff_lines(&expect, &got);

    // let result = TextDiff::from_lines(expect, got);
    if result.ratio() == 1.0 {
        buf.set_color(ColorSpec::new().set_fg(Some(Color::Yellow))).unwrap();
        write!(buf, "  <Differences in spans and line ending only.>").unwrap();
        buf.reset().unwrap();
        writeln!(buf).unwrap();
        false
    } else {
        print_diff(buf, result);
        false
    }
}

/// Normalize new lines between linux/windows for consistency
///
/// Remove \r (for Windows)
fn normalize_newlines(input: impl Into<String>) -> String {
    let input: String = input.into();
    let input = input.replace("\r", "");
    input
}

/// Replace numbered spans with "spanxxxx" for better diffs
fn normalize_spans(s: &str) -> String {
    use regex::Regex;
    let re1 = Regex::new(r"\[%#span[0-9]*\]").unwrap();
    let s = re1.replace_all(s, "[%#spanxxxx]");
    let re2 = Regex::new(r"let%span.*").unwrap();
    let s = re2.replace_all(&s, "let%span spanxxxx =");
    s.into_owned()
}

/// Normalize file path between linux/windows for consistency
///
/// Replace \ by /  (for Windows)
fn normalize_file_path(input: impl Into<String>) -> String {
    let input: String = input.into();
    let input = input.replace("\\", "/");
    input
}

fn differ(
    output: std::process::Output,
    stdout: &Path,
    stderr: &Path,
    should_succeed: bool,
) -> Result<(bool, Buffer), Box<dyn Error>> {
    let mut buf = Buffer::ansi();
    use std::str::from_utf8;
    match output.clone().ok() {
        Ok(output) => {
            let expect_out = &std::fs::read(stdout).unwrap_or_else(|_| Vec::new());
            let expect_err = &std::fs::read(stderr).unwrap_or_else(|_| Vec::new());

            let success_out =
                compare_str(&mut buf, from_utf8(&output.stdout)?, from_utf8(expect_out)?);
            let success_err =
                compare_str(&mut buf, from_utf8(&output.stderr)?, from_utf8(expect_err)?);

            Ok((success_out && success_err, buf))
        }
        Err(err) if should_succeed => {
            let output = err.as_output().unwrap();

            write!(buf, "{}", from_utf8(&output.stderr)?)?;
            // let success = compare_str(&mut buf, from_utf8(&output.stderr)?, from_utf8(expect_err)?);
            Ok((false, buf))
        }
        Err(err) => {
            let expect_err = &std::fs::read(stderr).unwrap_or_else(|_| Vec::new());

            let output = err.as_output().unwrap();
            let success = compare_str(&mut buf, from_utf8(&output.stderr)?, from_utf8(expect_err)?);
            Ok((success, buf))
        }
    }
}

fn print_diff<'a, W: WriteColor>(mut buf: W, diff: TextDiff<'a, 'a, 'a, str>) {
    // let mut last_lines: ArrayDeque<[_; 3], Wrapping> = ArrayDeque::new();
    let mut multiple_diffs = false;

    for ops in diff.grouped_ops(3) {
        for op in ops {
            for change in diff.iter_changes(&op) {
                let sign = match change.tag() {
                    ChangeTag::Delete => "-",
                    ChangeTag::Insert => "+",
                    ChangeTag::Equal => " ",
                };

                if change.tag() != ChangeTag::Equal {
                    if multiple_diffs {
                        write!(&mut buf, "...").unwrap();
                    }
                    let color = chunk_color(change.tag());
                    buf.set_color(&color).unwrap();
                    let index = change.old_index().or(change.new_index()).unwrap() + 1;

                    for line in change.value().lines() {
                        writeln!(&mut buf, "{} {:>2} ┊ {}", sign, index, line).unwrap();
                    }
                    buf.reset().unwrap();
                }
            }
        }
        multiple_diffs = true;
    }
    buf.reset().unwrap();
}

fn chunk_color(chunk: ChangeTag) -> ColorSpec {
    match chunk {
        ChangeTag::Equal => ColorSpec::new().set_fg(Some(Color::White)).clone(),
        ChangeTag::Delete => ColorSpec::new().set_fg(Some(Color::Red)).clone(),
        ChangeTag::Insert => ColorSpec::new().set_fg(Some(Color::Green)).clone(),
    }
}
