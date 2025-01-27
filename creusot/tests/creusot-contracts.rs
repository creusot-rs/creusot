use clap::Parser;
use std::{
    env,
    io::{IsTerminal, Write as _},
    path::PathBuf,
};
use termcolor::{BufferWriter, Color, ColorChoice, ColorSpec, StandardStream, WriteColor as _};

mod diff;
use diff::differ;

#[derive(Debug, Parser)]
struct Args {
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
    let mut args = Args::parse();
    if env::var("CI").is_ok() {
        args.force_color = true;
    }
    // Build creusot-rustc to make it available to cargo-creusot
    let creusot_rustc = escargot::CargoBuild::new()
        .bin("creusot-rustc")
        .current_release()
        .manifest_path("../creusot-rustc/Cargo.toml")
        .current_target()
        .run()
        .unwrap();
    let mut cargo_creusot = escargot::CargoBuild::new()
        .bin("cargo-creusot")
        .current_release()
        .manifest_path("../cargo-creusot/Cargo.toml")
        .current_target()
        .run()
        .unwrap()
        .command();
    let mut base_path = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    base_path.pop();

    std::process::Command::new("touch")
        .current_dir(&base_path)
        .args(["creusot-contracts/src/lib.rs"])
        .status()
        .unwrap();
    cargo_creusot.current_dir(&base_path).args([
        "creusot",
        "--creusot-rustc",
        creusot_rustc.path().to_str().unwrap(),
        "--stdout",
        "--export-metadata=false",
        "--span-mode=relative",
        "--spans-relative-to=creusot/tests/creusot-contracts",
        "--",
        "--package",
        "creusot-contracts",
    ]);

    let is_tty = std::io::stdout().is_terminal();
    let mut out = StandardStream::stdout(if args.force_color || is_tty {
        ColorChoice::Always
    } else {
        ColorChoice::Never
    });

    write!(out, "Testing creusot-contracts ... ").unwrap();
    out.flush().unwrap();

    let output = cargo_creusot.output().unwrap();
    let stdout = PathBuf::from("tests/creusot-contracts/creusot-contracts.coma");

    let mut failed = false;
    if args.bless {
        if output.stdout.is_empty() {
            panic!(
                "creusot-contracts should have an output! stderr is:\n\n{}",
                std::str::from_utf8(&output.stderr).unwrap()
            )
        }
        out.set_color(ColorSpec::new().set_fg(Some(Color::Blue))).unwrap();
        writeln!(&mut out, "blessed").unwrap();
        out.reset().unwrap();
        let (success, _) = differ(output.clone(), &stdout, None, true, is_tty).unwrap();

        if !success {
            out.set_color(ColorSpec::new().set_fg(Some(Color::Red))).unwrap();
            writeln!(&mut out, "failure").unwrap();
            out.reset().unwrap();
        }

        std::fs::write(stdout, &output.stdout).unwrap();
    } else {
        let (success, buf) = differ(output.clone(), &stdout, None, true, is_tty).unwrap();

        if success {
            out.set_color(ColorSpec::new().set_fg(Some(Color::Green))).unwrap();
            writeln!(&mut out, "ok").unwrap();
        } else {
            out.set_color(ColorSpec::new().set_fg(Some(Color::Red))).unwrap();
            writeln!(&mut out, "failure").unwrap();

            failed = true;
        };
        out.reset().unwrap();

        let wrt = BufferWriter::stdout(ColorChoice::Always);
        wrt.print(&buf).unwrap();
    }

    if failed {
        out.set_color(ColorSpec::new().set_fg(Some(Color::Red))).unwrap();
        drop(out);
        panic!("output of creusot-contracts failed");
    }
}
