use assert_cmd::output::OutputOkExt as _;
use regex::Regex;
use similar::{ChangeTag, TextDiff};
use std::{error::Error, io::Write as _, path::Path, str::from_utf8, sync::LazyLock};
use termcolor::{Buffer, Color, ColorSpec, WriteColor};

/// Normalize file path between linux/windows for consistency
///
/// Replace \ by /  (for Windows)
#[allow(unused)]
pub fn normalize_file_path(input: impl Into<String>) -> String {
    let input: String = input.into();
    let input = input.replace("\\", "/");
    input
}

pub fn differ(
    output: std::process::Output,
    stdout: &Path,
    stderr: Option<&Path>,
    should_succeed: bool,
    enable_color: bool,
) -> Result<(bool, Buffer), Box<dyn Error>> {
    let mut buf = if enable_color { Buffer::ansi() } else { Buffer::no_color() };
    match output.clone().ok() {
        Ok(output) => {
            let expect_out = &std::fs::read(stdout).unwrap_or_else(|_| Vec::new());
            let success_out =
                compare_str(&mut buf, from_utf8(&output.stdout)?, from_utf8(expect_out)?);

            let success_err = if let Some(stderr) = stderr {
                let expect_err = &std::fs::read(stderr).unwrap_or_else(|_| Vec::new());
                compare_str(&mut buf, from_utf8(&output.stderr)?, from_utf8(expect_err)?)
            } else {
                true
            };

            Ok((success_out && success_err, buf))
        }
        Err(err) if should_succeed => {
            let output = err.as_output().unwrap();

            write!(buf, "{}", from_utf8(&output.stderr)?)?;
            // let success = compare_str(&mut buf, from_utf8(&output.stderr)?, from_utf8(expect_err)?);
            Ok((false, buf))
        }
        Err(err) => {
            let Some(stderr) = stderr else { return Ok((true, buf)) };
            let expect_err = std::fs::read(stderr).unwrap_or_else(|_| Vec::new());

            let output = err.as_output().unwrap();
            let success =
                compare_str(&mut buf, from_utf8(&output.stderr)?, from_utf8(&expect_err)?);
            Ok((success, buf))
        }
    }
}

fn compare_str(buf: &mut Buffer, got: &str, expect: &str) -> bool {
    use similar::Algorithm;
    use std::time::Duration;

    let got = normalize_cargo_paths(got);
    let expect = normalize_cargo_paths(expect);
    if got == expect {
        return true;
    }

    let got = normalize_spans(&normalize_trailing_spaces(&normalize_newlines(&got)));
    let expect = normalize_spans(&normalize_trailing_spaces(&normalize_newlines(&expect)));

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
fn normalize_newlines(input: &str) -> String {
    let input: String = input.into();
    let input = input.replace("\r", "");
    input
}

/// Normalize trailing spaces
fn normalize_trailing_spaces(input: &str) -> String {
    let re = Regex::new(r"(?m)[\t ]*$").unwrap();
    let s = re.replace_all(input.into(), "");
    s.into_owned()
}

/// Replace numbered spans with "spanxxxx" for better diffs
fn normalize_spans(s: &str) -> String {
    let re1 = Regex::new(r"\[%#span[0-9]*\]").unwrap();
    let s = re1.replace_all(s, "[%#spanxxxx]");
    let re2 = Regex::new(r"let%span.*").unwrap();
    let s = re2.replace_all(&s, "let%span spanxxxx =");
    s.into_owned()
}

/// Replace relative paths to the cargo registry with an absolute path, and strip the hash.
///
/// For now this is only used when testing creusot-contracts.
fn normalize_cargo_paths(input: &str) -> String {
    static CARGO_REGISTRY: LazyLock<Regex> = LazyLock::new(|| {
        regex::Regex::new(r"(\.\.\/)*.cargo\/registry\/src\/index\.crates\.io-[a-zA-Z0-9]*")
            .unwrap()
    });
    CARGO_REGISTRY.replace_all(input, ".cargo/registry/src/index.crates.io").into()
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
