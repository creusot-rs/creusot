use clap::Parser;
use libc::{c_ushort, ioctl, STDOUT_FILENO, TIOCGWINSZ};
use std::{
    env,
    fs::File,
    io::{BufRead, BufReader, IsTerminal, Write},
    path::{Path, PathBuf},
    process::Command,
    sync::{
        atomic::{self, AtomicUsize},
        Mutex,
    },
    thread,
};
use termcolor::*;

mod diff;
use diff::{differ, normalize_file_path};

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
    /// Only run tests which contain this string
    filter: Option<String>,
}

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
    temp_file.push("creusot");
    temp_file.push("debug");
    temp_file.push("libcreusot_contracts.cmeta");

    let mut metadata_file = cargo_creusot;
    metadata_file.current_dir(base_path);
    metadata_file.arg("creusot").args(&[
        "--creusot-rustc".as_ref(),
        creusot_rustc.path().as_os_str(),
        "--metadata-path".as_ref(),
        temp_file.as_os_str(),
        "--output-file=/dev/null".as_ref(),
    ]);
    metadata_file.args(&["--", "--package", "creusot-contracts"]).env("CREUSOT_CONTINUE", "true");

    if !metadata_file.status().expect("could not dump metadata for `creusot_contracts`").success() {
        std::process::exit(1);
    }

    let mut args = Args::parse();
    if env::var("CI").is_ok() {
        args.quiet = true;
        args.force_color = true;
    }

    should_fail("tests/should_fail/**/*.rs", &args, |p| {
        run_creusot(creusot_rustc.path(), p, &temp_file.to_string_lossy())
    });
    should_succeed("tests/should_succeed/**/*.rs", &args, |p| {
        run_creusot(creusot_rustc.path(), p, &temp_file.to_string_lossy())
    });

    println!("All tests passed!");
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
    base_path.push("creusot");
    base_path.push("debug");

    let config_paths = creusot_setup::creusot_paths().unwrap();

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

    cmd.args(&["-Zno-codegen", "--crate-type=lib"]);
    cmd.args(&["--extern", &format!("creusot_contracts={}", creusot_contract_path)]);

    let mut dep_path = base_path;
    dep_path.push("deps");
    cmd.arg(format!("-Ldependency={}/", dep_path.display()));
    cmd.arg(file.file_name().unwrap());

    cmd.args(&[
        "--",
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

    Some(cmd)
}

fn should_succeed<B>(s: &str, args: &Args, b: B)
where
    B: Fn(&Path) -> Option<std::process::Command> + Send + Sync,
{
    glob_runner(s, args, b, true);
}

fn should_fail<B>(s: &str, args: &Args, b: B)
where
    B: Fn(&Path) -> Option<std::process::Command> + Send + Sync,
{
    glob_runner(s, args, b, false);
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

fn glob_runner<B>(s: &str, args: &Args, command_builder: B, should_succeed: bool)
where
    B: Fn(&Path) -> Option<std::process::Command> + Send + Sync,
{
    let is_tty = std::io::stdout().is_terminal();
    let out = StandardStream::stdout(if args.force_color || is_tty {
        ColorChoice::Always
    } else {
        ColorChoice::Never
    });

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
                            let (ref mut in_flight, ref mut out) = &mut *out;
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

                let (success, buf) =
                    differ(output.clone(), &stdout, Some(&stderr), should_succeed, is_tty).unwrap();

                let mut out = out.lock().unwrap();
                let (ref mut in_flight, ref mut out) = &mut *out;

                if !args.quiet {
                    if let Some(i) = in_flight.iter().position(|n| n == entry_name) {
                        in_flight.remove(i);
                    }
                }

                if args.bless {
                    if !success {
                        erase_in_flight(out);
                        write!(out, "{}: ", entry.display()).unwrap();
                        out.set_color(ColorSpec::new().set_fg(Some(Color::Blue))).unwrap();
                        writeln!(out, "blessed").unwrap();
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
                    if !success {
                        erase_in_flight(out);
                        write!(out, "{}: ", entry.display()).unwrap();
                        out.set_color(ColorSpec::new().set_fg(Some(Color::Red))).unwrap();
                        writeln!(out, "failure").unwrap();

                        test_failures.fetch_add(1, atomic::Ordering::SeqCst);
                    };
                    out.reset().unwrap();
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
    let (_, mut out) = out.into_inner().unwrap();

    if test_failures > 0 {
        out.set_color(ColorSpec::new().set_fg(Some(Color::Red))).unwrap();
        writeln!(&mut out, "{test_failures} failures out of {test_count} tests").unwrap();
        drop(out);
        std::process::exit(1);
    }
}
