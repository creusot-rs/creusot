use assert_cmd::prelude::*;
use std::fs::File;
use std::io::{BufRead, BufReader, Write};
use std::process::{exit, Command};
use termcolor::*;

fn main() {
    let why3_path = std::env::var("WHY3_PATH").unwrap_or_else(|_| "why3".into());
    let config_path = std::env::var("WHY3_CONFIG");
    let mut out = StandardStream::stdout(ColorChoice::Always);
    let orange = Color::Ansi256(214);
    let lazy = std::env::args().any(|arg| arg == "--lazy");

    let filter = std::env::args().nth(1);

    let mut success = true;
    let mut obsolete = false;
    for file in glob::glob("../creusot/tests/should_succeed/**/*.rs").unwrap() {
        let mut file = file.unwrap();

        if let Some(ref filter) = filter {
            if !file.to_str().map(|file| file.contains(filter)).unwrap_or(false) {
                continue;
            }
        }

        let header_line =
            BufReader::new(File::open(&file).unwrap()).lines().nth(0).unwrap().unwrap();

        file.set_extension("mlcfg");

        write!(&mut out, "Testing {} ... ", file.display()).unwrap();
        out.flush().unwrap();

        if header_line.contains("WHY3SKIP") {
            out.set_color(ColorSpec::new().set_fg(Some(Color::Yellow))).unwrap();
            writeln!(&mut out, "skipped").unwrap();
            out.reset().unwrap();
            continue;
        }

        let mut sessiondir = file.clone();
        sessiondir.set_file_name(file.file_stem().unwrap());

        let mut sessionfile = sessiondir.clone();
        sessionfile.push("why3session.xml");

        let output;
        if sessionfile.is_file() {
            // There is a session directory. Try to replay the session.
            let mut command = Command::new(why3_path.clone());
            command.arg("replay");
            command.args(&["-L", "../prelude"]);
            if lazy {
                command.arg("--obsolete-only");
            }
            if let Ok(ref config) = config_path {
                command.args(&["-C", config]);
                // command.arg(&format!("--extra-config={config}"));
            }
            command.arg(sessiondir);
            output = command.ok();
            if output.is_ok() {
                let outputstring = std::str::from_utf8(&output.as_ref().unwrap().stderr).unwrap();
                if outputstring.contains("[Warning] session is obsolete")
                    || outputstring.contains("[Warning] session is obsolete")
                {
                    out.set_color(ColorSpec::new().set_fg(Some(orange))).unwrap();
                    writeln!(&mut out, "obsolete").unwrap();
                    obsolete = true;
                } else {
                    out.set_color(ColorSpec::new().set_fg(Some(Color::Green))).unwrap();
                    writeln!(&mut out, "replayed").unwrap();
                }
                out.reset().unwrap();
            }
        } else {
            // No session directory. Simply parse the file using "why3 prove".
            let mut command = Command::new(why3_path.clone());
            command.arg("prove");
            command.args(&["-L", "../prelude", "-F", "mlcfg"]);
            command.arg(file);
            output = command.ok();
            if output.is_ok() {
                out.set_color(ColorSpec::new().set_fg(Some(Color::Green))).unwrap();
                writeln!(&mut out, "syntax ok").unwrap();
                out.reset().unwrap();
            }
        }

        if !output.is_ok() {
            out.set_color(ColorSpec::new().set_fg(Some(Color::Red))).unwrap();
            writeln!(&mut out, "failure").unwrap();
            out.reset().unwrap();

            let output = output.unwrap_err();
            eprint!("{output}");
            let output = output.as_output().unwrap();

            writeln!(&mut out, "{}", std::str::from_utf8(&output.stdout).unwrap()).unwrap();

            success = false;
            if lazy {
                break;
            }
        }
    }

    if success {
        if obsolete {
            write!(&mut out, "Some of session files were ").unwrap();
            out.set_color(ColorSpec::new().set_fg(Some(orange))).unwrap();
            write!(&mut out, "obsolete").unwrap();
            out.reset().unwrap();
            writeln!(&mut out, ".").unwrap();
            exit(2)
        } else {
            out.set_color(ColorSpec::new().set_fg(Some(Color::Green))).unwrap();
            write!(&mut out, "Success").unwrap();
            out.reset().unwrap();
            writeln!(&mut out, "!").unwrap();
            exit(0)
        }
    } else {
        out.set_color(ColorSpec::new().set_fg(Some(Color::Red))).unwrap();
        write!(&mut out, "Failure").unwrap();
        out.reset().unwrap();
        writeln!(&mut out, "!").unwrap();
        exit(1)
    }
}
