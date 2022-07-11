use assert_cmd::prelude::*;
use std::fs::File;
use std::io::{BufRead, BufReader, Write};
use std::process::{exit, Command};
use termcolor::*;
use git2::Repository;
use std::path::PathBuf;
use clap::Parser;

#[derive(Parser, Debug)]
struct Args {
    #[clap(long = "lazy")]
    lazy: bool,
    #[clap(long = "diff-from")]
    diff_from: Option<String>,
    #[clap(long = "fail-obsolete")]
    fail_obsolete: bool,
    #[clap(long = "skip-unstable")]
    skip_unstable: bool,
    filter: Option<String>,
}

fn main() {
    let args = Args::parse();

    eprintln!("{args:?}");

    let why3_path = std::env::var("WHY3_PATH").unwrap_or_else(|_| "why3".into());
    let config_path = std::env::var("WHY3_CONFIG");
    let mut out = StandardStream::stdout(ColorChoice::Always);
    let orange = Color::Ansi256(214);

    let changed = if let Some(diff) = args.diff_from {
        Some(changed_mlcfgs(&diff).unwrap())
    } else {
        None
    };

    let mut success = true;
    let mut obsolete = false;
    for file in glob::glob("../creusot/tests/should_succeed/**/*.rs").unwrap() {
        let mut file = file.unwrap();

        if let Some(ref filter) = args.filter {
            if !file.to_str().map(|file| file.contains(filter)).unwrap_or(false) {
                continue;
            }
        }

        file.set_extension("mlcfg");

        if let Some(changed_list) = &changed {
            let file = file.strip_prefix("../").unwrap().to_owned();

            if !changed_list.contains(&file) {
                continue;
            }
        }

        let header_line =
            BufReader::new(File::open(&file).unwrap()).lines().nth(0).unwrap().unwrap();

        write!(&mut out, "Testing {} ... ", file.display()).unwrap();
        out.flush().unwrap();

        if header_line.contains("WHY3SKIP") || (args.skip_unstable && header_line.contains("UNSTABLE")) {
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
        let mut command = Command::new(why3_path.clone());
        command.arg("--debug=ignore_unused_vars");
        if sessionfile.is_file() {
            // There is a session directory. Try to replay the session.
            command.arg("replay");
            command.args(&["-L", "../prelude"]);
            if args.lazy {
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
                if outputstring.contains("[Warning] session is obsolete") {
                    out.set_color(ColorSpec::new().set_fg(Some(orange))).unwrap();
                    writeln!(&mut out, "obsolete").unwrap();
                    obsolete = true;
                    if args.lazy && args.fail_obsolete {
                        break;
                    }
                } else if outputstring
                    .contains("[Warning] found detached goals or theories or transformations")
                {
                    out.set_color(ColorSpec::new().set_fg(Some(orange))).unwrap();
                    writeln!(&mut out, "detached goals").unwrap();
                    obsolete = true;
                    if args.lazy && args.fail_obsolete {
                        break;
                    }
                } else {
                    out.set_color(ColorSpec::new().set_fg(Some(Color::Green))).unwrap();
                    writeln!(&mut out, "replayed").unwrap();
                }
                out.reset().unwrap();
            }
        } else {
            // No session directory. Simply parse the file using "why3 prove".
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
            let output = output.as_output().unwrap();

            writeln!(&mut out, "******** STDOUT ********").unwrap();
            writeln!(&mut out, "{}", std::str::from_utf8(&output.stdout).unwrap()).unwrap();
            writeln!(&mut out, "******** STDERR ********").unwrap();
            writeln!(&mut out, "{}", std::str::from_utf8(&output.stderr).unwrap()).unwrap();
            writeln!(&mut out, "************************").unwrap();

            success = false;
            if args.lazy {
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
            if args.fail_obsolete {
                exit(1)
            }
        } else {
            out.set_color(ColorSpec::new().set_fg(Some(Color::Green))).unwrap();
            write!(&mut out, "Success").unwrap();
            out.reset().unwrap();
            writeln!(&mut out, "!").unwrap();
        }
    } else {
        out.set_color(ColorSpec::new().set_fg(Some(Color::Red))).unwrap();
        write!(&mut out, "Failure").unwrap();
        out.reset().unwrap();
        writeln!(&mut out, "!").unwrap();
        exit(1)
    }
}


fn changed_mlcfgs(from: &str) -> Result<Vec<PathBuf>, git2::Error> {
    let repo = Repository::open("..")?;
    let rev = repo.revparse_single(from)?.id();
    let commit = repo.find_commit(rev)?;
    let diff = repo.diff_tree_to_workdir_with_index(Some(&commit.tree()?), None)?;

    let mut paths = Vec::new();
    for d in diff.deltas() {
        if let Some(path) = d.new_file().path() {
            if path.extension().map(|e| e == "mlcfg").unwrap_or(false) {
                paths.push(path.to_owned());
            }
         }
    }
    Ok(paths)
}