use clap::Parser;
use libc::{STDOUT_FILENO, TIOCGWINSZ, c_ushort, ioctl};
use std::{
    env,
    fs::{self, File},
    io::{BufRead, BufReader, IsTerminal, Write},
    path::{Path, PathBuf},
    process::Command,
    sync::{
        Mutex,
        atomic::{self, AtomicUsize},
    },
    thread,
};
use termcolor::*;

mod diff;
use diff::differ;

macro_rules! writeln_color {
    ($out:expr, $color:expr, $($arg:tt)*) => {
        $out.set_color(ColorSpec::new().set_fg(Some($color))).unwrap();
        writeln!($out, $($arg)*).unwrap();
        $out.reset().unwrap();
    };
}

/// Used to query the size of the terminal
#[derive(Default)]
#[repr(C)]
struct TermSize {
    row: c_ushort,
    col: c_ushort,
    x: c_ushort,
    y: c_ushort,
}

#[derive(Debug, Parser)]
struct Args {
    /// Suppress all output other than failing test cases
    #[clap(long)]
    quiet: bool,
    /// Force color output
    #[clap(long)]
    force_color: bool,
    /// Overwrite expected output files with actual output
    #[clap(long)]
    bless: bool,
    #[clap(long)]
    with_spans: bool,
    /// Run #[erasure] checks on creusot-std (and only that)
    #[clap(long)]
    erasure_check: bool,
    /// Only run tests which contain this string
    filter: Option<String>,
}

impl Args {
    fn stream(&self) -> StandardStream {
        StandardStream::stdout(if self.force_color {
            ColorChoice::Always
        } else {
            ColorChoice::Never
        })
    }
}

fn main() {
    let mut args = Args::parse();
    if env::var("CI").is_ok() {
        args.quiet = true;
        args.force_color = true;
    } else {
        args.force_color = args.force_color || std::io::stdout().is_terminal();
    }
    // Go to the root of the creusot repository.
    std::env::set_current_dir("..").unwrap();
    build_creusot_rustc(args.force_color);
    build_cargo_creusot(args.force_color);

    let base_path = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let paths = CreusotPaths::new(base_path.parent().unwrap());

    if args.erasure_check {
        erasure_check(&paths);
        return;
    }

    let mut test_creusot_std = true;
    if let Some(ref filter) = args.filter {
        if !"tests/creusot-std/creusot-std.rs".contains(filter) {
            test_creusot_std = false;
        }
    }
    let contracts_success = translate_creusot_std(&args, &paths, test_creusot_std);

    let (mut failed, mut total) =
        (if contracts_success { 0 } else { 1 }, if test_creusot_std { 1 } else { 0 });
    let (fail1, total1) = should_fail("tests/should_fail/**/*.rs", &args, |p| {
        run_creusot(p, &paths, args.with_spans)
    });
    let (fail2, total2) = should_succeed("tests/should_succeed/**/*.rs", &args, |p| {
        run_creusot(p, &paths, args.with_spans)
    });

    total += total1 + total2;
    failed += fail1 + fail2;
    if failed > 0 {
        let mut out = args.stream();
        writeln_color!(out, Color::Red, "{failed} failures out of {total} tests");
        drop(out);
        std::process::exit(1);
    }

    println!("All tests passed!");
}

const CARGO_CREUSOT: &str = "target/debug/cargo-creusot";
const CREUSOT_RUSTC: &str = "target/debug/creusot-rustc";

fn build_creusot_rustc(force_color: bool) {
    cargo_build("creusot-rustc", force_color)
}

fn build_cargo_creusot(force_color: bool) {
    cargo_build("cargo-creusot", force_color)
}

fn cargo_build(target: &str, force_color: bool) {
    println! {"Building {target}..."};
    let mut cargo = Command::new("cargo");
    cargo.args(["build", "--bin", target]);
    if force_color {
        cargo.args(["--color", "always"]);
    }
    let output = cargo.output().unwrap();
    if !output.status.success() {
        std::io::stdout().write_all(&output.stderr).unwrap();
        std::process::exit(1)
    }
}

struct CreusotPaths {
    creusot_rustc: PathBuf,
    deps: PathBuf,
    rlib: PathBuf,
    cmeta: PathBuf,
}

impl CreusotPaths {
    fn new(base: &Path) -> Self {
        let creusot = base.join("target/creusot/debug");
        Self {
            creusot_rustc: base.join(CREUSOT_RUSTC),
            deps: creusot.join("deps"),
            rlib: creusot.join("libcreusot_std.rlib"),
            cmeta: creusot.join("libcreusot_std.cmeta"),
        }
    }
}

/// Returns `false` if the translation changed
///
/// This will only check the output of `creusot-std` if `test_creusot_std` is true.
fn translate_creusot_std(args: &Args, paths: &CreusotPaths, test_creusot_std: bool) -> bool {
    if test_creusot_std {
        print!("Translating creusot-std... ");
        std::io::stdout().flush().unwrap();
        std::process::Command::new("touch").args(["creusot-std/src/lib.rs"]).status().unwrap();
    }
    let mut build = build_creusot_std(paths, true, ErasureCheck::No, args.with_spans);
    let mut out = args.stream();
    let output = build.output().expect("could not translate `creusot_std`");
    if !output.status.success() {
        writeln_color!(out, Color::Red, "could not translate");
        out.flush().unwrap();
        eprintln!("{}", String::from_utf8(output.stderr).unwrap());
        std::process::exit(1);
    }

    if !test_creusot_std {
        return true;
    }

    let expect = PathBuf::from("tests/creusot-std/creusot-std.coma");
    let mut succeeded = true;
    let (success, buf) = differ(output.clone(), &expect, None, true, args.force_color).unwrap();

    // Warnings in creusot-std will be counted as an error at the end,
    // but we still allow --bless so we can experiment without resolving warnings immediately.
    if !output.stderr.is_empty() {
        writeln_color!(out, Color::Yellow, "warnings");
        out.flush().unwrap();
        eprintln!("{}", std::str::from_utf8(&output.stderr).unwrap());
        succeeded = false;
    }

    if args.bless {
        if output.stdout.is_empty() {
            panic!("creusot-std should have an output!")
        }

        if success {
            writeln_color!(out, Color::Green, "unchanged");
        } else {
            writeln_color!(out, Color::Blue, "blessed");
            std::fs::write(expect, &output.stdout).unwrap();
        }
    } else {
        if success {
            writeln_color!(out, Color::Green, "ok");
        } else {
            writeln_color!(out, Color::Red, "failure");
            succeeded = false;
        };

        let wrt = BufferWriter::stdout(ColorChoice::Always);
        wrt.print(&buf).unwrap();
        out.flush().unwrap();
    }

    succeeded
}

enum ErasureCheck {
    No,
    Warn,
    Error,
}

fn build_creusot_std(
    paths: &CreusotPaths,
    output_cmeta: bool,
    erasure_check: ErasureCheck,
    with_spans: bool,
) -> Command {
    let mut build = Command::new(CARGO_CREUSOT);
    build.arg("creusot"); // cargo creusot
    build.arg(match erasure_check {
        ErasureCheck::No => "--erasure-check=no",
        ErasureCheck::Warn => "--erasure-check=warn",
        ErasureCheck::Error => "--erasure-check=error",
    });
    if output_cmeta {
        build.args(["--creusot-extern", &format!("creusot_std={}", paths.cmeta.display())]);
    } else {
        build.arg("--export-metadata=false");
    }
    if with_spans {
        build.arg("--span-mode=relative");
    } else {
        build.arg("--span-mode=off");
    }
    build.args(["--no-check-version", "--stdout", "--spans-relative-to=tests/creusot-std"]);
    build.arg("--creusot-rustc").arg(&paths.creusot_rustc);
    build.args(["--", "--package", "creusot-std", "--quiet"]).env("CREUSOT_CONTINUE", "true");
    if matches!(erasure_check, ErasureCheck::Warn | ErasureCheck::Error) {
        build.arg("-Zbuild-std=core,std");
    }
    build
}

fn run_creusot(
    file: &Path,
    paths: &CreusotPaths,
    with_spans: bool,
) -> Option<std::process::Command> {
    // Magic comment with instructions for creusot
    let header_line = BufReader::new(File::open(&file).unwrap()).lines().nth(0).unwrap().unwrap();
    if header_line.contains("UISKIP") {
        return None;
    }

    let mut cmd = Command::new(&paths.creusot_rustc);
    cmd.current_dir(file.parent().unwrap());

    // Find comment chunks of the form CREUSOT_ARG=ARGUMENT. Does not support spaces in arguments currently (would require real parser)
    let args: Vec<_> = header_line
        .split(" ")
        .filter_map(|chunk| {
            let (first, rest) = chunk.split_once("=")?;
            if first != "CREUSOT_ARG" { None } else { Some(rest) }
        })
        .collect();

    cmd.args(&["--edition=2024", "-Zno-codegen", "--crate-type=lib"]);
    cmd.args(&["--extern", &format!("creusot_std={}", paths.rlib.display())]);
    cmd.arg(format!("-Ldependency={}/", paths.deps.display()));
    cmd.arg(file.file_name().unwrap());

    if header_line.contains("SHORT_ERROR") {
        cmd.arg("--error-format=short");
    }
    cmd.args(&[
        "--",
        "--stdout",
        "--export-metadata=false",
        // we will write the coma output next to the .rs file
        "--spans-relative-to=.",
    ]);
    if !args.iter().any(|arg| arg.starts_with("--span-mode")) {
        if with_spans {
            cmd.arg("--span-mode=relative");
        } else {
            cmd.arg("--span-mode=off");
        }
    }
    cmd.args(args);
    cmd.args(&["--creusot-extern", &format!("creusot_std={}", paths.cmeta.display())]);

    Some(cmd)
}

fn should_succeed<B>(s: &str, args: &Args, b: B) -> (usize, usize)
where
    B: Fn(&Path) -> Option<std::process::Command> + Send + Sync,
{
    glob_runner(s, args, b, true)
}

fn should_fail<B>(s: &str, args: &Args, b: B) -> (usize, usize)
where
    B: Fn(&Path) -> Option<std::process::Command> + Send + Sync,
{
    glob_runner(s, args, b, false)
}

/// Replace global paths in `s` with ".", provided `s` is in fact a string.
fn erase_global_paths(s: &mut Vec<u8>) {
    let mut base_path = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    base_path.pop();
    let base_path = base_path.display().to_string();

    let Ok(err) = std::str::from_utf8(s) else { return };
    if err.contains(&base_path) {
        let new_stderr = err.replacen(&base_path, ".", usize::MAX);
        *s = new_stderr.into();
    }
}

/// Returns `(tests failed, total tests)`
fn glob_runner<B>(s: &str, args: &Args, command_builder: B, should_succeed: bool) -> (usize, usize)
where
    B: Fn(&Path) -> Option<std::process::Command> + Send + Sync,
{
    let out = args.stream();
    let test_count = AtomicUsize::new(0);
    let test_failures = AtomicUsize::new(0);

    let entries = Mutex::new(glob::glob(s).expect("Failed to read glob pattern"));
    let nb_threads = thread::available_parallelism().map(|n| n.into()).unwrap_or(1usize);
    let out = Mutex::new((Vec::new(), out));

    // Print all test currently running
    let write_in_flight = |in_flight: &Vec<String>, out: &mut StandardStream| {
        // get terminal width
        let mut size: TermSize = TermSize::default();
        unsafe { ioctl(STDOUT_FILENO, TIOCGWINSZ.into(), &mut size as *mut _) };
        let width = size.col as usize;
        // Save cursor position
        write!(out, "\x1b7").unwrap();
        let mut wrote = 0;
        write!(out, "Testing: ").unwrap();
        wrote += "Testing: ".len();
        for (i, name) in (&*in_flight).iter().enumerate() {
            if i != 0 {
                write!(out, ", ").unwrap();
                wrote += ", ".len();
            }
            if wrote + name.len() + 5 > width {
                // Do not overflow the line, or output breaks!
                write!(out, "...").unwrap();
                break;
            }
            write!(out, "{name}").unwrap();
            wrote += name.len();
        }
        // restore cursor position (put it back at the beginning of the line)
        write!(out, "\x1b8").unwrap();
        out.flush().unwrap();
    };
    // erase after the cursor to the end of the screen
    let erase_in_flight = |out: &mut StandardStream| write!(out, "\x1b[J").unwrap();

    thread::scope(|s| {
        let worker = || {
            // invariant: the cursor is always at the start of the line where we should write `Testing ...`
            loop {
                let Some(entry) = entries.lock().unwrap().next() else {
                    return;
                };
                test_count.fetch_add(1, atomic::Ordering::SeqCst);
                let entry = entry.unwrap();

                if let Some(ref filter) = args.filter {
                    if !entry.to_str().map(|entry| entry.contains(filter)).unwrap_or(false) {
                        continue;
                    }
                }

                let entry_name = entry.file_stem().unwrap().to_str().unwrap();

                let output = match command_builder(&entry) {
                    None => continue,
                    Some(mut c) => {
                        if !args.quiet {
                            let mut out = out.lock().unwrap();
                            let (in_flight, out) = &mut *out;
                            in_flight.push(entry_name.to_string());
                            erase_in_flight(out);
                            write_in_flight(in_flight, out);
                        }
                        let mut o = c.output().unwrap();
                        // Replace global paths in stderr with (a simulacrum of) local paths
                        erase_global_paths(&mut o.stderr);
                        o
                    }
                };

                let stderr = entry.with_extension("stderr");
                let stdout = entry.with_extension("coma");

                let (success, buf) = differ(
                    output.clone(),
                    &stdout,
                    Some(&stderr),
                    should_succeed,
                    args.force_color,
                )
                .unwrap();

                let mut out = out.lock().unwrap();
                let (in_flight, out) = &mut *out;

                if !args.quiet {
                    if let Some(i) = in_flight.iter().position(|n| n == entry_name) {
                        in_flight.remove(i);
                    }
                }

                if args.bless && !(should_succeed && !output.status.success()) {
                    if output.stdout.is_empty() {
                        let _ = std::fs::remove_file(stdout);
                    } else {
                        std::fs::write(stdout, &output.stdout).unwrap();
                    }

                    let no_warn = output.stderr.is_empty();
                    if no_warn {
                        let _ = std::fs::remove_file(stderr);
                    } else {
                        std::fs::write(stderr, &output.stderr).unwrap();
                    }

                    if !success {
                        erase_in_flight(out);
                        write!(out, "{}: ", entry.display()).unwrap();
                        if args.with_spans {
                            writeln_color!(out, Color::Blue, "blessed with spans");
                        } else if no_warn {
                            writeln_color!(out, Color::Blue, "blessed");
                        } else {
                            writeln_color!(out, Color::Magenta, "blessed (with warnings)");
                        }
                    }
                } else {
                    if !success {
                        erase_in_flight(out);
                        write!(out, "{}: ", entry.display()).unwrap();
                        writeln_color!(out, Color::Red, "failure");
                        test_failures.fetch_add(1, atomic::Ordering::SeqCst);
                    };
                    out.flush().unwrap();

                    let wrt = BufferWriter::stdout(ColorChoice::Always);
                    wrt.print(&buf).unwrap();
                }
                if !args.quiet {
                    erase_in_flight(out);
                    if !in_flight.is_empty() {
                        write_in_flight(in_flight, out);
                    }
                }
            }
        };
        let mut handles = Vec::new();
        for _ in 0..nb_threads {
            handles.push(s.spawn(worker));
        }
    });

    let test_count = test_count.load(atomic::Ordering::SeqCst);
    let test_failures = test_failures.load(atomic::Ordering::SeqCst);

    (test_failures, test_count)
}

/// This test runs on its own because it sets `-Zbuild-std`
/// which slows things down.
fn erasure_check(paths: &CreusotPaths) {
    let build_once = |erasure_check, msg: &str| {
        print!("{msg}");
        std::io::stdout().flush().unwrap();
        let mut build = build_creusot_std(paths, false, erasure_check, false);
        let output = build.output().unwrap();
        if !output.status.success() {
            println!("failed");
            if !output.stderr.is_empty() {
                println!("{}", std::str::from_utf8(&output.stderr).unwrap());
            }
            std::process::exit(1)
        }
        println!("ok")
    };
    // The first build is in warning mode
    // (1) in case there is a stale _creusot_erasure/creusot_std (it get rewritten at the end)
    // (2) to check that warning mode doesn't error
    build_once(ErasureCheck::Warn, "Collect #[erasure] requests... ");
    fs::remove_dir_all("target/creusot").unwrap();
    build_once(ErasureCheck::Error, "Check #[erasure]... ");
}
