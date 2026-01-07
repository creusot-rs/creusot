use assert_cmd::prelude::*;
use clap::Parser;
use git2::Repository;
use regex::Regex;
use std::{
    env,
    fs::File,
    io::{BufRead, BufReader, IsTerminal, Write},
    path::PathBuf,
    process::{Command, exit},
};
use termcolor::*;

#[derive(Parser, Debug)]
struct Args {
    /// Update proof.json files
    #[clap(long)]
    update: bool,
    /// Minimize proof.json files
    #[clap(long)]
    minimize: bool,
    /// Only check coma files that differ from the provided source in the git history (useful for small PRs)
    #[clap(long = "diff-from")]
    diff_from: Option<String>,
    /// Fail as soon as a single test fails
    #[clap(long = "fail-early")]
    fail_early: bool,
    /// Suppress all output other than failing test cases
    #[clap(long)]
    quiet: bool,
    /// Force color output
    #[clap(long)]
    force_color: bool,
    /// Ignore why3find cache
    #[clap(long)]
    no_cache: bool,
    /// Only run tests which contain this string
    filter: Option<String>,
}

fn main() {
    let mut args = Args::parse();
    if env::var("CI").is_ok() {
        args.force_color = true;
    }

    let is_tty = std::io::stdout().is_terminal();
    let mut out = StandardStream::stdout(if args.force_color || is_tty {
        ColorChoice::Always
    } else {
        ColorChoice::Never
    });

    let orange = Color::Ansi256(214);
    let tactic_re = Regex::new(r"TACTIC (\S*)").unwrap();
    let time_re = Regex::new(r"TIME (\d+)").unwrap();

    std::env::set_current_dir("..").unwrap();

    // Use the Creusot installation for Why3, Why3find, and solvers (because they're a pain to keep track of if we allow them to come from anywhere)
    let paths = creusot_setup::creusot_paths();

    // Use the local prelude, so that it's easy to test quick changes.
    let build_prelude = Command::new("cargo").args(["run", "--bin", "prelude-generator"]).status();
    if !build_prelude.unwrap().success() {
        panic!("prelude-generator failed");
    };

    let changed =
        if let Some(diff) = args.diff_from { Some(changed_comas(&diff).unwrap()) } else { None };

    let mut success = true;
    let mut obsolete = false;
    for file in glob::glob("tests/**/*.coma").unwrap() {
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
            if !changed_list.iter().any(|p| *p == file) {
                continue;
            }
        }

        let rs_file = File::open(&file.with_extension("rs"))
            .unwrap_or_else(|_| panic!("no rust file for {:?}", file));
        let header_line = BufReader::new(rs_file).lines().next().unwrap().unwrap();

        // Default (not `quiet`): print "Testing tests/current/test ... " and flush before running the test
        // if `quiet` enabled: postpone printing, store the message in `current`, only print it if the test case fails
        let mut current: &str = &format!("Testing {} ... ", file.display());
        if !args.quiet {
            write!(out, "{current}").unwrap();
            current = "";
            out.flush().unwrap();
        }

        if header_line.contains("WHY3SKIP") {
            write!(out, "{current}").unwrap();
            out.set_color(ColorSpec::new().set_fg(Some(Color::Yellow))).unwrap();
            writeln!(out, "skipped").unwrap();
            out.reset().unwrap();
            continue;
        }

        let should_fail = file.to_str().map(|file| file.contains("should_fail")).unwrap_or(false);

        let mut sessiondir = file.clone();
        sessiondir.set_file_name(file.file_stem().unwrap());

        let output;
        let library = paths.prelude().join("packages/creusot").display().to_string();
        let mut why3 = Command::new(paths.why3());
        why3.arg("-C").arg(paths.why3_conf());
        why3.arg("--warn-off=unused_variable");
        why3.arg("--warn-off=clone_not_abstract");
        why3.arg("--warn-off=axiom_abstract");
        why3.arg("--debug=coma_no_trivial,stack_trace");

        if header_line.contains("WHY3PROVE")
            || file.file_name().unwrap() == "creusot-contracts.coma"
        {
            if sessiondir.join("proof.json").is_file() {
                write!(out, "{current}").unwrap();
                out.set_color(ColorSpec::new().set_fg(Some(Color::Red))).unwrap();
                writeln!(&mut out, "unused proof.json").unwrap();
                out.reset().unwrap();
                success = false;
            }

            let sessionfile = sessiondir.join("why3session.xml");
            if !sessionfile.is_file() {
                out.set_color(ColorSpec::new().set_fg(Some(Color::Red))).unwrap();
                writeln!(&mut out, "missing why3 session").unwrap();
                out.reset().unwrap();
                success = false;
                continue;
            }

            let Some(proved) =
                BufReader::new(File::open(&sessionfile).unwrap()).lines().find_map(|l| {
                    match l.unwrap().as_str() {
                        "<file format=\"coma\">" => Some(false),
                        "<file format=\"coma\" proved=\"true\">" => Some(true),
                        _ => None,
                    }
                })
            else {
                writeln!(out, "{current}error").unwrap();
                success = false;
                continue;
            };

            if !proved && !should_fail {
                write!(out, "{current}").unwrap();
                out.set_color(ColorSpec::new().set_fg(Some(orange))).unwrap();
                writeln!(&mut out, "not proved").unwrap();
                out.reset().unwrap();

                success = false;
                continue;
            }
            if proved && should_fail {
                write!(out, "{current}").unwrap();
                out.set_color(ColorSpec::new().set_fg(Some(orange))).unwrap();
                writeln!(&mut out, "proof exists").unwrap();
                out.reset().unwrap();

                success = false;
                continue;
            }

            // There is a session directory. Try to replay the session.
            why3.arg("replay");
            why3.args(&["-L", &library]);
            why3.arg(sessiondir.clone());

            output = why3.ok();
            if let Ok(output) = &output {
                let outputstring = std::str::from_utf8(&output.stderr).unwrap();

                match session_obsolete(outputstring) {
                    Obsolete::Obsolete => {
                        obsolete = true;
                        write!(out, "{current}").unwrap();
                        out.set_color(ColorSpec::new().set_fg(Some(orange))).unwrap();
                        writeln!(&mut out, "obsolete").unwrap();
                    }
                    Obsolete::Detached => {
                        obsolete = true;
                        write!(out, "{current}").unwrap();
                        out.set_color(ColorSpec::new().set_fg(Some(orange))).unwrap();
                        writeln!(&mut out, "detached goals").unwrap();
                    }
                    Obsolete::Good => {
                        if !args.quiet {
                            if is_tty {
                                // Move to beginning of line and clear line.
                                write!(out, "\x1b[G\x1b[2K").unwrap();
                            } else {
                                out.set_color(ColorSpec::new().set_fg(Some(Color::Green))).unwrap();
                                writeln!(out, "replayed").unwrap();
                            }
                        }
                    }
                }
                out.reset().unwrap();
            }
        } else if header_line.contains("NO_REPLAY") {
            // Simply parse the file using "why3 prove".
            why3.arg("prove");
            why3.args(&["-L", &library, "-F", "coma"]);
            why3.arg(file);
            output = why3.ok();
            if output.is_ok() && !args.quiet {
                if is_tty {
                    // Move to beginning of line and clear line.
                    write!(out, "\x1b[G\x1b[2K").unwrap();
                } else {
                    out.set_color(ColorSpec::new().set_fg(Some(Color::Green))).unwrap();
                    writeln!(out, "syntax ok").unwrap();
                }
            }
        } else {
            let sessionfiles = ["why3session.xml", "why3shapes.gz"]
                .into_iter()
                .filter(|file| sessiondir.join(file).is_file())
                .collect::<Vec<_>>();
            if sessionfiles.len() > 0 {
                write!(out, "{current}").unwrap();
                out.set_color(ColorSpec::new().set_fg(Some(Color::Red))).unwrap();
                writeln!(&mut out, "unused {sessionfiles:?}. Please do not use Why3 sessions files for this test. Instead, update the proof.json file.").unwrap();
                out.reset().unwrap();
                success = false;
            }

            let mut why3find = Command::new(paths.why3find());
            why3find.env("WHY3CONFIG", paths.why3_conf());
            why3find.env("DUNE_DIR_LOCATIONS", "why3find:lib:target/creusot/");
            why3find.arg("prove").arg(file.canonicalize().unwrap());
            if let Some(tactic) = tactic_re.captures_iter(&header_line).next() {
                why3find.args(["--tactic", tactic.get(1).unwrap().as_str()]);
            }
            if let Some(time) = time_re.captures_iter(&header_line).next() {
                why3find.args(["--time", time.get(1).unwrap().as_str()]);
            }
            if args.no_cache {
                why3find.arg("--no-cache");
            }
            if !args.update {
                why3find.arg("-r");
            }
            if args.minimize {
                why3find.arg("-m");
            }

            output = why3find.ok();
            if output.is_ok() && !args.quiet {
                if is_tty {
                    // Move to beginning of line and clear line.
                    write!(out, "\x1b[G\x1b[2K").unwrap();
                } else {
                    out.set_color(ColorSpec::new().set_fg(Some(Color::Green))).unwrap();
                    writeln!(&mut out, "proved").unwrap();
                }
            }
            out.reset().unwrap();
        }

        if let Err(output) = output {
            write!(out, "{current}").unwrap();
            out.set_color(ColorSpec::new().set_fg(Some(Color::Red))).unwrap();
            writeln!(&mut out, "failure").unwrap();
            out.reset().unwrap();

            if let Some(output) = output.as_output() {
                // why3 returned an error code
                writeln!(&mut out, "******** STDOUT ********").unwrap();
                out.write_all(&output.stdout).unwrap();
                writeln!(&mut out, "******** STDERR ********").unwrap();
                out.write_all(&output.stderr).unwrap();
                writeln!(&mut out, "************************").unwrap();
            } else {
                // there was an issue launching the why3 command
                writeln!(&mut out, "{output}").unwrap();
                return;
            }

            success = false;
        }
    }

    // Fail if there are proofs or sessions without a coma file.
    for file in glob::glob("tests/**/proof.json")
        .unwrap()
        .chain(glob::glob("tests/**/why3session.xml").unwrap())
        .chain(glob::glob("tests/**/why3shapes.gz").unwrap())
    {
        let file = file.unwrap();
        let coma = file.parent().unwrap().with_extension("coma");
        if !coma.is_file() {
            out.set_color(ColorSpec::new().set_fg(Some(Color::Red))).unwrap();
            writeln!(&mut out, "unused {file:?}").unwrap();
            out.reset().unwrap();
            success = false;
        }
    }

    if success {
        if obsolete {
            write!(&mut out, "Some session files were ").unwrap();
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
    let repo = Repository::open(".")?;
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
