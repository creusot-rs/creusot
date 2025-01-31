use clap::Parser;
use std::{
    env,
    fs::File,
    io::{BufRead, BufReader, IsTerminal, Write},
    path::{Path, PathBuf},
    process::Command,
};
use termcolor::*;

mod diff;
use diff::{differ, normalize_file_path};

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
    B: Fn(&Path) -> Option<std::process::Command>,
{
    glob_runner(s, args, b, true);
}

fn should_fail<B>(s: &str, args: &Args, b: B)
where
    B: Fn(&Path) -> Option<std::process::Command>,
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
    B: Fn(&Path) -> Option<std::process::Command>,
{
    let is_tty = std::io::stdout().is_terminal();
    let mut out = StandardStream::stdout(if args.force_color || is_tty {
        ColorChoice::Always
    } else {
        ColorChoice::Never
    });

    let mut test_count = 0;
    let mut test_failures = 0;

    for entry in glob::glob(s).expect("Failed to read glob pattern") {
        test_count += 1;
        let entry = entry.unwrap();

        if let Some(ref filter) = args.filter {
            if !entry.to_str().map(|entry| entry.contains(filter)).unwrap_or(false) {
                continue;
            }
        }
        let output = match command_builder(&entry) {
            None => continue,
            Some(mut c) => {
                let mut o = c.output().unwrap();
                // Replace global paths in stderr with (a simulacrum of) local paths
                erase_global_paths(&mut o.stderr);
                o
            }
        };

        let stderr = entry.with_extension("stderr");
        let stdout = entry.with_extension("coma");

        // Default (not `quiet`): print "Testing tests/current/test ... " and flush before running the test
        // if `quiet` enabled: postpone printing, store the message in `current`, only print it if the test case fails
        let mut current: &str = &format!("Testing {} ... ", entry.display());
        if !args.quiet {
            write!(out, "{}", current).unwrap();
            current = "";
            out.flush().unwrap();
        }

        if args.bless {
            let (success, _) =
                differ(output.clone(), &stdout, Some(&stderr), should_succeed, is_tty).unwrap();

            if success {
                if is_tty {
                    // Move to beginning of line and clear line.
                    write!(out, "\x1b[G\x1b[2K").unwrap();
                } else {
                    out.set_color(ColorSpec::new().set_fg(Some(Color::Green))).unwrap();
                    writeln!(out, "ok").unwrap();
                }
            } else {
                write!(out, "{current}").unwrap();
                out.set_color(ColorSpec::new().set_fg(Some(Color::Blue))).unwrap();
                writeln!(&mut out, "blessed").unwrap();
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
            let (success, buf) =
                differ(output.clone(), &stdout, Some(&stderr), should_succeed, is_tty).unwrap();

            if success {
                if !args.quiet {
                    if is_tty {
                        // Move to beginning of line and clear line.
                        write!(out, "\x1b[G\x1b[2K").unwrap();
                    } else {
                        out.set_color(ColorSpec::new().set_fg(Some(Color::Green))).unwrap();
                        writeln!(out, "ok").unwrap();
                    }
                }
            } else {
                write!(out, "{current}").unwrap();
                out.set_color(ColorSpec::new().set_fg(Some(Color::Red))).unwrap();
                writeln!(&mut out, "failure").unwrap();

                test_failures += 1;
            };
            out.reset().unwrap();

            let wrt = BufferWriter::stdout(ColorChoice::Always);
            wrt.print(&buf).unwrap();
        }
    }

    if test_failures > 0 {
        out.set_color(ColorSpec::new().set_fg(Some(Color::Red))).unwrap();
        writeln!(&mut out, "{test_failures} failures out of {test_count} tests").unwrap();
        drop(out);
        std::process::exit(1);
    }
}
