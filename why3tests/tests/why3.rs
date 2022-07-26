use assert_cmd::prelude::*;
use clap::Parser;
use git2::Repository;
use std::{
    fs::File,
    io::{BufRead, BufReader, Write},
    path::PathBuf,
    process::{exit, Command},
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
    /// Only check mlcfg files that differ from the provided source in the git history (useful for small PRs)
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
    let why3_path = std::env::var("WHY3_PATH").unwrap_or_else(|_| "why3".into());
    let config_path = std::env::var("WHY3_CONFIG");
    let mut out = StandardStream::stdout(ColorChoice::Always);
    let orange = Color::Ansi256(214);

    let changed =
        if let Some(diff) = args.diff_from { Some(changed_mlcfgs(&diff).unwrap()) } else { None };

    let mut success = true;
    let mut obsolete = false;
    for file in glob::glob("../creusot/tests/should_succeed/**/*.rs").unwrap() {
        let mut file = file.unwrap();

        if let Some(ref filter) = args.filter {
            if !file.to_str().map(|file| file.contains(filter)).unwrap_or(false) {
                continue;
            }
        }

        if let Some(changed_list) = &changed {
            let mut file = file.strip_prefix("../").unwrap().to_owned();
            file.set_extension("mlcfg");

            if !changed_list.contains(&file) {
                continue;
            }
        }

        let header_line =
            BufReader::new(File::open(&file).unwrap()).lines().nth(0).unwrap().unwrap();

        file.set_extension("mlcfg");

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

            match args.replay {
                ReplayLevel::None => {
                    command.arg("--merging-only");
                }

                ReplayLevel::Obsolete => {
                    command.arg("--obsolete-only");
                }
                ReplayLevel::All => {}
            };

            if let Ok(ref config) = config_path {
                command.args(&["-C", config]);
                // command.arg(&format!("--extra-config={config}"));
            }
            command.arg(sessiondir);
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
        }

        // Check for early abort
        if args.fail_early && (!success || obsolete) {
            break;
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
