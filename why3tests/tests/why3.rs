use clap::Parser;
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
    /// Timeout in seconds, does not override the TIME comment in .rs files
    #[clap(long)]
    time: Option<f64>,
    /// Multiply all timeouts by this factor
    /// The `--time=N` option must also be provided for the factor to affect tests without explicit TIME comments
    /// We use this option to run tests on especially slow machines, like CI.
    #[clap(long, default_value_t = 1.)]
    time_factor: f64,
    /// Max parallel provers
    #[clap(short = 'j')]
    jobs: Option<usize>,
    /// Only run tests which contain one of these strings
    filter: Vec<String>,
}

enum OtherTest {
    Why3find {
        tactic: Option<String>,
        time: Option<f64>,
        depth: Option<String>,
    },
    Why3 {
        /// If None, only check Coma syntax using `why3 prove`, paradoxically.
        /// If Some, contains directory of session file, as expected by `why3 replay`.
        prove: Option<PathBuf>,
    },
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
    let time_re = Regex::new(r"TIME ((\d|\.)+)").unwrap();
    let depth_re = Regex::new(r"DEPTH ((\d|\.)+)").unwrap();

    std::env::set_current_dir("..").unwrap();

    // Use the Creusot installation for Why3, Why3find, and solvers (because they're a pain to keep track of if we allow them to come from anywhere)
    let paths = creusot_setup::creusot_paths();

    // Use the local prelude, so that it's easy to test quick changes.
    let build_prelude = Command::new("cargo").args(["run", "--bin", "prelude-generator"]).status();
    if !build_prelude.unwrap().success() {
        panic!("prelude-generator failed");
    };

    let changed = if let Some(diff) = args.diff_from { Some(changed_comas(&diff)) } else { None };

    let mut success = true;
    let mut obsolete = false;
    let mut default_tests = vec![];
    let mut other_tests = vec![];
    let coma_files = [
        "examples/**/*.coma",
        "tests/creusot-std/verif/**/*.coma",
        "tests/should_succeed/**/*.coma",
        "tests/should_fail/**/*.coma",
    ]
    .into_iter()
    .flat_map(|s| glob::glob(s).unwrap());
    for file in coma_files {
        let file = file.unwrap();

        if !args.filter.is_empty()
            && !args
                .filter
                .iter()
                .any(|filter| file.to_str().is_some_and(|file| file.contains(filter)))
        {
            continue;
        }

        if let Some(changed_list) = &changed {
            if !changed_list.iter().any(|p| *p == file) {
                continue;
            }
        }

        let (has_rs_file, header_line) = match File::open(&file.with_extension("rs")) {
            Err(_) => (false, String::new()),
            Ok(rs_file) => (true, BufReader::new(rs_file).lines().next().unwrap().unwrap()),
        };

        if header_line.contains("WHY3SKIP") {
            continue;
        }

        let mut sessiondir = file.clone();
        sessiondir.set_file_name(file.file_stem().unwrap());
        let sessionfile = sessiondir.join("why3session.xml");

        if header_line.contains("WHY3PROVE") || (!has_rs_file && sessionfile.is_file()) {
            let proof_json = sessiondir.join("proof.json");
            if proof_json.is_file() {
                out.set_color(ColorSpec::new().set_fg(Some(Color::Red))).unwrap();
                writeln!(&mut out, "unused {}", proof_json.display()).unwrap();
                out.reset().unwrap();
                success = false;
            }

            if !sessionfile.is_file() {
                out.set_color(ColorSpec::new().set_fg(Some(Color::Red))).unwrap();
                writeln!(&mut out, "missing why3 session").unwrap();
                out.reset().unwrap();
                success = false;
                continue;
            }

            other_tests.push((file, OtherTest::Why3 { prove: Some(sessiondir) }));
        } else if header_line.contains("NO_REPLAY") {
            other_tests.push((file, OtherTest::Why3 { prove: None }));
        } else {
            let sessionfiles = ["why3session.xml", "why3shapes.gz"]
                .into_iter()
                .filter(|file| sessiondir.join(file).is_file())
                .collect::<Vec<_>>();
            if sessionfiles.len() > 0 {
                out.set_color(ColorSpec::new().set_fg(Some(Color::Red))).unwrap();
                writeln!(&mut out, "unused {sessionfiles:?}. Please do not use Why3 sessions files for this test. Instead, update the proof.json file.").unwrap();
                out.reset().unwrap();
                success = false;
            }
            let tactic = tactic_re.captures_iter(&header_line).next().map(|c| c[1].to_owned());
            let time = time_re
                .captures_iter(&header_line)
                .next()
                .map(|c| c[1].to_owned().parse().unwrap());
            let depth = depth_re.captures_iter(&header_line).next().map(|c| c[1].to_owned());
            if tactic.is_none() && time.is_none() && depth.is_none() {
                default_tests.push(file);
            } else {
                other_tests.push((file, OtherTest::Why3find { tactic, time, depth }));
            }
        }
    }

    let library = std::env::current_dir().unwrap().join("target/creusot");

    let jobs = &format!("{}", args.jobs.unwrap_or_else(creusot_setup::default_provers_parallelism));
    let why3find = || {
        let mut why3find = Command::new(paths.why3find());
        why3find
            .env("PATH", paths.bin())
            .env("WHY3CONFIG", paths.creusot_why3_conf())
            .env("DUNE_DIR_LOCATIONS", &format!("why3find:lib:{}", library.display()))
            .arg("prove")
            .arg("--no-autodetect-provers")
            .args(["-j", jobs]);
        if let Some(time) = args.time {
            why3find.args(["--time", &format!("{}", time * args.time_factor)]);
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
        why3find
    };

    let why3 = || {
        let mut why3 = Command::new(paths.why3());
        why3.env("PATH", paths.bin());
        why3.arg("-C").arg(paths.user_why3_conf());
        why3.arg("--extra-config").arg(paths.creusot_why3_conf());
        why3.arg("--warn-off=unused_variable");
        why3.arg("--warn-off=clone_not_abstract");
        why3.arg("--warn-off=axiom_abstract");
        why3.arg("--debug=coma_no_trivial,stack_trace");
        why3
    };

    // Run default tests as a single why3find invocation
    if !default_tests.is_empty() {
        writeln!(out, "Default tests ({} files)...", default_tests.len()).unwrap();
        // `spawn` to inherit stdout
        let result = why3find().args(default_tests).spawn().unwrap().wait().unwrap();
        success &= result.success();
    }

    for (file, test) in other_tests {
        // Check for early abort
        if args.fail_early && (!success || obsolete) {
            break;
        }

        // Default (not `quiet`): print "Testing tests/current/test ... " and flush before running the test
        // if `quiet` enabled: postpone printing, store the message in `current`, only print it if the test case fails
        let mut current: &str = &format!("Testing {} ... ", file.display());
        if !args.quiet {
            write!(out, "{current}").unwrap();
            current = "";
            out.flush().unwrap();
        }

        let output;

        match test {
            OtherTest::Why3find { tactic, time, depth } => {
                let mut why3find = why3find();
                if let Some(tactic) = tactic {
                    why3find.args(["--tactic", &tactic]);
                }
                if let Some(time) = time {
                    why3find.args(["--time", &format!("{}", time * args.time_factor)]);
                }
                if let Some(depth) = depth {
                    why3find.args(["--depth", &depth]);
                }
                why3find.arg(file);
                output = why3find.output().unwrap();
                if !args.quiet && output.status.success() {
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
            OtherTest::Why3 { prove: Some(sessiondir) } => {
                let sessionfile = sessiondir.join("why3session.xml");
                let Some(proved) = BufReader::new(File::open(&sessionfile).unwrap())
                    .lines()
                    .find_map(|l| match l.unwrap().as_str() {
                        "<file format=\"coma\">" => Some(false),
                        "<file format=\"coma\" proved=\"true\">" => Some(true),
                        _ => None,
                    })
                else {
                    writeln!(out, "{current}error").unwrap();
                    success = false;
                    continue;
                };

                let should_fail =
                    file.to_str().map(|file| file.contains("should_fail")).unwrap_or(false);

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
                let library = library.join("packages/creusot").display().to_string();
                let mut why3 = why3();
                why3.arg("replay");
                why3.args(&["-L", &library]);
                why3.arg(sessiondir);

                output = why3.output().unwrap();
                if output.status.success() {
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
                                    out.set_color(ColorSpec::new().set_fg(Some(Color::Green)))
                                        .unwrap();
                                    writeln!(out, "replayed").unwrap();
                                }
                            }
                        }
                    }
                    out.reset().unwrap();
                }
            }
            OtherTest::Why3 { prove: None } => {
                // Simply parse the file using "why3 prove".
                let library = library.join("packages/creusot").display().to_string();
                let mut why3 = why3();
                why3.arg("prove");
                why3.args(&["-L", &library, "-F", "coma"]);
                why3.arg(file);
                output = why3.output().unwrap();
                if !args.quiet && output.status.success() {
                    if is_tty {
                        // Move to beginning of line and clear line.
                        write!(out, "\x1b[G\x1b[2K").unwrap();
                    } else {
                        out.set_color(ColorSpec::new().set_fg(Some(Color::Green))).unwrap();
                        writeln!(out, "syntax ok").unwrap();
                    }
                }
            }
        }

        if !output.status.success() {
            write!(out, "{current}").unwrap();
            out.set_color(ColorSpec::new().set_fg(Some(Color::Red))).unwrap();
            writeln!(&mut out, "failure").unwrap();
            out.reset().unwrap();
            writeln!(&mut out, "******** STDOUT ********").unwrap();
            out.write_all(&output.stdout).unwrap();
            writeln!(&mut out, "******** STDERR ********").unwrap();
            out.write_all(&output.stderr).unwrap();
            writeln!(&mut out, "************************").unwrap();
            success = false;
        }
    }

    // Fail if there are proofs or sessions without a coma file.
    let proof_files = ["examples", "tests"].into_iter().flat_map(|dir| {
        ["proof.json", "why3session.xml", "why3shapes.gz"]
            .into_iter()
            .flat_map(|base| glob::glob(&(dir.to_owned() + "/**/" + base)).unwrap())
    });
    for file in proof_files {
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

fn changed_comas(from: &str) -> Vec<PathBuf> {
    let output = Command::new("git")
        .args(["diff", "--name-only", from, "tests", "examples"])
        .output()
        .unwrap();
    if !output.status.success() {
        panic!("git diff failed")
    }
    output
        .stdout
        .lines()
        .filter_map(|line| {
            let path = PathBuf::from(line.unwrap());
            if path.extension().is_some_and(|e| e == "coma") { Some(path) } else { None }
        })
        .collect()
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
