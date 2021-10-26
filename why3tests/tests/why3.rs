use assert_cmd::prelude::*;
use std::fs::File;
use std::io::{BufRead, BufReader, Write};
use std::process::{exit, Command};
use termcolor::*;

fn main() {
    let why3_path = std::env::var("WHY3_PATH").unwrap_or_else(|_| "why3".into());
    let mut out = StandardStream::stdout(ColorChoice::Always);

    let filter = std::env::args().nth(1);

    let mut success = true;
    for file in glob::glob("../creusot/tests/should_succeed/**/*.rs").unwrap() {
        let mut file = file.unwrap();

        if let Some(ref filter) = filter {
            if !file.to_str().map(|file| file.contains(filter)).unwrap_or(false) {
                continue;
            }
        }

        let header_line =
            BufReader::new(File::open(&file).unwrap()).lines().nth(0).unwrap().unwrap();

        file.set_extension("stdout");

        write!(&mut out, "Testing {} ... ", file.display()).unwrap();

        if header_line.contains("WHY3SKIP") {
            out.set_color(ColorSpec::new().set_fg(Some(Color::Yellow))).unwrap();
            writeln!(&mut out, "skipped").unwrap();
            out.reset().unwrap();
            continue;
        }

        let mut command = Command::new(why3_path.clone());
        command.arg("prove");
        command.args(&["-L", "../prelude"]);
        command.arg(file);

        let mut has_prover = false;
        let do_proof = header_line.contains("WHY3PROVE");
        if do_proof {
            command.args(&["-a", "split_vc"]);
            if header_line.contains("Z3") {
                has_prover = true;
                command.arg("-Pz3");
            }
            if header_line.contains("CVC4") {
                has_prover = true;
                command.arg("-Pcvc4");
            }
        }

        let output = command.ok();
        if output.is_ok() {
            out.set_color(ColorSpec::new().set_fg(Some(Color::Green))).unwrap();
            if do_proof {
                if has_prover {
                    writeln!(&mut out, "proved").unwrap();
                } else {
                    out.set_color(ColorSpec::new().set_fg(Some(Color::Red))).unwrap();
                    writeln!(&mut out, "no prover").unwrap();
                }
            } else {
                writeln!(&mut out, "ok").unwrap();
            }
        } else {
            out.set_color(ColorSpec::new().set_fg(Some(Color::Red))).unwrap();
            writeln!(&mut out, "failure").unwrap();
        }
        out.reset().unwrap();

        if !output.is_ok() {
            success = false;
            let output = output.unwrap_err();
            let output = output.as_output().unwrap();
            writeln!(&mut out, "{}", std::str::from_utf8(&output.stderr).unwrap()).unwrap();
        }
    }

    if !success {
        exit(1);
    }
}
