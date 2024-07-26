use assert_cmd::prelude::*;
use clap::Parser;
use git2::Repository;
use std::{
    fs::File,
    io::{BufRead, BufReader, Write},
    path::PathBuf,
    process::exit,
};
use termcolor::*;

#[derive(clap::ValueEnum, Debug, Clone)]
enum ReplayLevel {
    None,
    Obsolete,
    All,
}

#[derive(Parser, Debug)]
struct Args {
    /// Only check that a session merges and contains no obsolete goals
    #[clap(long = "replay", value_enum, default_value_t=ReplayLevel::All)]
    replay: ReplayLevel,
    /// Only check coma files that differ from the provided source in the git history (useful for small PRs)
    #[clap(long = "diff-from")]
    diff_from: Option<String>,
    /// Fail as soon as a single test fails
    #[clap(long = "fail-early")]
    fail_early: bool,

    /// Skip any files which are marked with `UNSTABLE` on the first line
    #[clap(long = "skip-unstable")]
    skip_unstable: bool,
    /// Only run tests which contain this string
    filter: Option<String>,
}

fn main() {
    let args = Args::parse();

    let mut out = StandardStream::stdout(ColorChoice::Always);
    let orange = Color::Ansi256(214);

    let changed =
        if let Some(diff) = args.diff_from { Some(changed_comas(&diff).unwrap()) } else { None };

    let mut success = true;
    let mut obsolete = false;
    for file in glob::glob("../creusot/tests/**/*.coma").unwrap() {
        // Check for early abort
        if args.fail_early && (!success || obsolete) {
            break;
        }

        let file = file.unwrap();

        if let Some(ref filter) = args.filter {
            if !file.to_str().map(|file| file.contains(filter)).unwrap_or(false) {
                continue;
            }
        }

        if let Some(changed_list) = &changed {
            let file = file.strip_prefix("../").unwrap();
            if !changed_list.iter().any(|p| p == file) {
                continue;
            }
        }

        let rs_file = File::open(&file.with_extension("rs"))
            .unwrap_or_else(|_| panic!("no rust file for {:?}", file));
        let header_line = BufReader::new(rs_file).lines().nth(0).unwrap().unwrap();

        write!(&mut out, "Testing {} ... ", file.display()).unwrap();
        out.flush().unwrap();

        if header_line.contains("WHY3SKIP")
            || (args.skip_unstable && header_line.contains("UNSTABLE"))
        {
            out.set_color(ColorSpec::new().set_fg(Some(Color::Yellow))).unwrap();
            writeln!(&mut out, "skipped").unwrap();
            out.reset().unwrap();
            continue;
        }

        let should_fail = file.to_str().map(|file| file.contains("should_fail")).unwrap_or(false);

        let mut sessiondir = file.clone();
        sessiondir.set_file_name(file.file_stem().unwrap());

        let mut sessionfile = sessiondir.clone();
        sessionfile.push("why3session.xml");

        let output;
        let mut command = creusot_dev_config::why3_command().unwrap();
        command.arg("--warn-off=unused_variable");
        command.arg("--warn-off=clone_not_abstract");
        command.arg("--warn-off=axiom_abstract");
        command.arg("--debug=coma_no_trivial");

        if sessionfile.is_file() {
            let Some(proved) =
                BufReader::new(File::open(&sessionfile).unwrap()).lines().find_map(|l| {
                    match l.unwrap().as_str() {
                        "<file format=\"coma\">" => Some(false),
                        "<file format=\"coma\" proved=\"true\">" => Some(true),
                        _ => None,
                    }
                })
            else {
                writeln!(&mut out, "error").unwrap();
                success = false;
                continue;
            };

            if !proved {
                let color = if should_fail { Color::Green } else { orange };
                out.set_color(ColorSpec::new().set_fg(Some(color))).unwrap();
                writeln!(&mut out, "not proved").unwrap();
                out.reset().unwrap();

                success &= should_fail;
                continue;
            } else if should_fail {
                out.set_color(ColorSpec::new().set_fg(Some(orange))).unwrap();
                writeln!(&mut out, "proof exists").unwrap();
                out.reset().unwrap();

                success = false;
                continue;
            }

            // There is a session directory. Try to replay the session.
            command.arg("replay");
            command.args(&["-L", ".."]);

            match args.replay {
                ReplayLevel::None => {
                    command.arg("--merging-only");
                }

                ReplayLevel::Obsolete => {
                    command.arg("--obsolete-only");
                }
                ReplayLevel::All => {}
            };

            command.arg(sessiondir.clone());
            output = command.ok();
            if output.is_ok() {
                let outputstring = std::str::from_utf8(&output.as_ref().unwrap().stderr).unwrap();

                match session_obsolete(outputstring) {
                    Obsolete::Obsolete => {
                        obsolete = true;
                        out.set_color(ColorSpec::new().set_fg(Some(orange))).unwrap();
                        writeln!(&mut out, "obsolete").unwrap();
                    }
                    Obsolete::Detached => {
                        obsolete = true;
                        out.set_color(ColorSpec::new().set_fg(Some(orange))).unwrap();
                        writeln!(&mut out, "detached goals").unwrap();
                    }
                    Obsolete::Good => {
                        out.set_color(ColorSpec::new().set_fg(Some(Color::Green))).unwrap();
                        writeln!(&mut out, "replayed").unwrap();
                    }
                }
                out.reset().unwrap();
            }
        } else {
            // No session directory. Simply parse the file using "why3 prove".
            command.arg("prove");
            command.args(&["-L", "..", "-F", "coma"]);
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
        }
    }

    if success {
        if obsolete {
            write!(&mut out, "Some of session files were ").unwrap();
            out.set_color(ColorSpec::new().set_fg(Some(orange))).unwrap();
            write!(&mut out, "obsolete").unwrap();
            out.reset().unwrap();
            writeln!(&mut out, ".").unwrap();
            exit(1)
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

fn changed_comas(from: &str) -> Result<Vec<PathBuf>, git2::Error> {
    let repo = Repository::open("..")?;
    let rev = repo.revparse_single(from)?.id();
    let commit = repo.find_commit(rev)?;
    let diff = repo.diff_tree_to_workdir_with_index(Some(&commit.tree()?), None)?;

    let mut paths = Vec::new();
    for d in diff.deltas() {
        if let Some(path) = d.new_file().path() {
            if path.extension().map(|e| e == "coma").unwrap_or(false) {
                paths.push(path.to_owned());
            }
        }
    }
    Ok(paths)
}

enum Obsolete {
    Obsolete,
    Detached,
    Good,
}

fn session_obsolete(outputstring: &str) -> Obsolete {
    if outputstring.contains("[Warning] session is obsolete") {
        Obsolete::Obsolete
    } else if outputstring.contains("[Warning] found detached goals or theories or transformations")
    {
        Obsolete::Detached
    } else {
        Obsolete::Good
    }
}
