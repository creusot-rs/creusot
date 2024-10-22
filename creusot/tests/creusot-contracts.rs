use std::{io::Write as _, path::PathBuf};
use termcolor::{BufferWriter, Color, ColorChoice, ColorSpec, StandardStream, WriteColor as _};

mod diff;
use diff::differ;

fn main() {
    let bless = std::env::args().any(|arg| arg == "--bless");
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
        "--stdout",
        "--export-metadata=false",
        "--span-mode=relative",
        // FIXME: spans disappear if this this set to something else
        "--spans-relative-to=.",
        "--",
        "--package",
        "creusot-contracts",
    ]);

    let output = cargo_creusot.output().unwrap();
    let mut out = StandardStream::stdout(ColorChoice::Always);

    let stdout = PathBuf::from("tests/creusot-contracts/creusot-contracts.coma");

    let mut failed = false;
    if bless {
        out.set_color(ColorSpec::new().set_fg(Some(Color::Blue))).unwrap();
        writeln!(&mut out, "blessed").unwrap();
        out.reset().unwrap();
        let (success, _) = differ(output.clone(), &stdout, None, true).unwrap();

        if !success {
            out.set_color(ColorSpec::new().set_fg(Some(Color::Red))).unwrap();
            writeln!(&mut out, "failure").unwrap();
            out.reset().unwrap();
        }

        std::fs::write(stdout, &output.stdout).unwrap();
    } else {
        let (success, mut buf) = differ(output.clone(), &stdout, None, true).unwrap();

        if success {
            out.set_color(ColorSpec::new().set_fg(Some(Color::Green))).unwrap();
            writeln!(&mut out, "ok").unwrap();
        } else {
            out.set_color(ColorSpec::new().set_fg(Some(Color::Red))).unwrap();
            writeln!(&mut out, "failure").unwrap();

            failed = true;
        };
        out.reset().unwrap();

        buf.reset().unwrap();
        let wrt = BufferWriter::stdout(ColorChoice::Always);
        wrt.print(&buf).unwrap();
    }

    if failed {
        out.set_color(ColorSpec::new().set_fg(Some(Color::Red))).unwrap();
        drop(out);
        panic!("output of creusot-contracts failed");
    }
}
