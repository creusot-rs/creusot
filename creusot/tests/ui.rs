use assert_cmd::prelude::*;
use std::path::Path;
use std::path::PathBuf;
use std::process::Command;
use std::env;

use dissimilar::*;

use termcolor::*;
use std::io::Write;
use arraydeque::{ArrayDeque, Wrapping};
use std::error::Error;

fn main () {
    should_fail("tests/should_fail/*.rs", run_creusot);
    should_succeed("tests/should_succeed/*.rs", run_creusot);
}

fn run_creusot(file: &Path) -> std::process::Command {
    let mut cmd = Command::cargo_bin("creusot").unwrap();
    let mut d = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    d.pop();
    d.push("target");
    d.push("debug");

    cmd.envs(env::vars());
    cmd.arg(format!("-L{}/", d.display()));
    cmd.arg(format!("{}", file.display()));
    cmd
}

fn should_succeed<B>(s: &str, b: B)
where B: Fn(&Path) -> std::process::Command
{
    glob_runner(s, b, should_succeed_case);
}

fn should_fail<B>(s: &str, b: B)
where B: Fn(&Path) -> std::process::Command
{
    glob_runner(s, b, should_fail_case);
}

fn glob_runner<B, C>(s: &str, b: B, c: C)
where B : Fn(&Path) -> std::process::Command,
        C : Fn(std::process::Output, &Path, &Path) -> Result<(bool, Buffer), Box<dyn Error>>
    {
    let mut out = StandardStream::stdout(ColorChoice::Always);

    let mut test_count = 0;
    let mut test_failures = 0;
    let bless =  std::env::args().any(|arg| arg == "--bless");
    let filter = std::env::args().nth(1);

    for entry in glob::glob(s).expect("Failed to read glob pattern") {
        test_count += 1;
        let entry = entry.unwrap();

        if let Some(ref filter) = filter {
            if !entry.to_str().map(|entry| entry.contains(filter)).unwrap_or(false) {
                continue;
            }
        }
        let output = b(&entry).output().unwrap();

        let stderr = entry.with_extension("stderr");
        let stdout = entry.with_extension("stdout");

        write!(&mut out, "Testing {} ... ", entry.display()).unwrap();

        if bless {
            out.set_color(ColorSpec::new().set_fg(Some(Color::Blue))).unwrap();
            writeln!(&mut out, "blessed").unwrap();
            out.reset().unwrap();

            // if output.stderr.is_empty() {
            //     let _ = std::fs::remove_file(stderr);
            // } else {
            //     std::fs::write(stderr, &output.stderr).unwrap();
            // }
            if output.stdout.is_empty() {
                let _ = std::fs::remove_file(stdout);
            } else {
                std::fs::write(stdout, &output.stdout).unwrap();
            }
        } else {
            let (success, buf) = c(output, &stdout, &stderr).unwrap();

            if success {
                out.set_color(ColorSpec::new().set_fg(Some(Color::Green))).unwrap();
                writeln!(&mut out, "ok").unwrap();
            } else {
                out.set_color(ColorSpec::new().set_fg(Some(Color::Red))).unwrap();
                writeln!(&mut out, "failure").unwrap();

                test_failures += 1;
            };
            out.reset().unwrap();

            BufferWriter::stdout(ColorChoice::Always).print(&buf).unwrap();
        }

    }

    if test_failures > 0 {
        panic!("{} failures out of {} tests", test_failures, test_count);
    }

}

fn compare_str(buf: &mut Buffer, got: &str, expect: &str) -> bool {
    let result = diff(expect, got);

    match result[..] {
        [Chunk::Equal(_)] => { true },
        _ => {
            print_diff(buf, result);
            false
        }
    }
}

fn should_succeed_case(output: std::process::Output, stdout: &Path, _stderr: &Path) -> Result<(bool, Buffer), Box<dyn Error>> {
    let output = output.unwrap();
    let mut buf = Buffer::ansi();
    use std::str::from_utf8;
    let expect = &std::fs::read(stdout).unwrap_or_else(|_| Vec::new());
    let gotten = &output.stdout;

    let success = compare_str(&mut buf, &from_utf8(gotten)?, &from_utf8(expect)?);

    // TODO: enable stderr comparisons
    // let expect = &std::fs::read(stderr).unwrap_or_else(|_| Vec::new());;
    // let gotten = &output.stderr;

    // success &= compare_str(&mut buf, &from_utf8(gotten)?, &from_utf8(expect)?);

    Ok((success, buf))
}

fn should_fail_case(output: std::process::Output, _stdout: &Path, _stderr: &Path) -> Result<(bool, Buffer), Box<dyn Error>> {
    let buf = Buffer::ansi();
    Ok((!output.status.success(), buf))
}


fn print_diff<W : WriteColor>(mut buf: W, diff: Vec<Chunk>) {
    let mut line_count = 0;
    let mut last_lines : ArrayDeque<[_; 3], Wrapping> = ArrayDeque::new();
    let mut multiple_diffs = false;
    for chunk in diff {
        // Print context
        if print_chunk(chunk) {
            if multiple_diffs {
                writeln!(&mut buf, ".....").unwrap();
            }
            for (num, l) in &last_lines {
                writeln!(&mut buf, "{:>4} {}", num, l).unwrap();
            }
            last_lines.clear();
            multiple_diffs = true;
        }

        for l in chunk_str(chunk).lines() {
            if print_chunk(chunk) {
                buf.set_color(&chunk_color(chunk)).unwrap();
                writeln!(&mut buf, "{:>4} {}", line_count, l).unwrap();
            } else {
                last_lines.push_back((line_count, l));
            }
            line_count += 1;
        }
        buf.set_color(&ColorSpec::new()).unwrap();
    }
}

fn chunk_color(chunk: Chunk) -> ColorSpec {
    match chunk {
        Chunk::Equal(_) => ColorSpec::new(),
        Chunk::Delete(_) => { let mut c = ColorSpec::new(); c.set_fg(Some(Color::Red)); c},
        Chunk::Insert(_) => { let mut c = ColorSpec::new(); c.set_fg(Some(Color::Green)); c},
    }
}
fn print_chunk(chunk: Chunk) -> bool {
    if let Chunk::Equal(_) = chunk {
        false
    } else {
        true
    }
}

fn chunk_str(chunk: Chunk) -> &str {
    match chunk {
        Chunk::Equal(s) => s,
        Chunk::Delete(s) => s,
        Chunk::Insert(s) => s,
    }
}
