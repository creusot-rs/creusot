use anyhow::{Result, anyhow};
use clap::*;
use creusot_setup::{Paths, creusot_paths};
use std::{ffi::OsStr, path::PathBuf, process::Command};

use crate::{
    OUTPUT_PREFIX,
    why3_launcher::{self, Why3Mode},
};

#[derive(Debug, Parser)]
pub struct ProveArgs {
    /// Run Why3 IDE after proof search.
    #[clap(flatten)]
    pub ide: ProveIdeWhen,
    /// Replay proofs only, no update.
    #[clap(long)]
    pub replay: bool,
    /// Generate Why3 sessions for why3 ide.
    #[clap(long)]
    pub why3session: bool,
    /// Files to prove; default to everything in `verif/`.
    pub files: Vec<PathBuf>,
}

// Although these two options look similar, they are implemented quite differently.
// - `ide_on_fail` just corresponds to `why3find`'s `-i` flag.
// - `ide_always` is implemented in a more ad hoc way here.
#[derive(Clone, Debug, Parser)]
#[group(multiple = false)]
pub struct ProveIdeWhen {
    /// Run why3find and open the IDE on unproved goals only.
    #[clap(long, short = 'i')]
    ide_on_fail: bool,
    /// Run why3find and open the IDE on a single Coma file.
    #[clap(long)]
    ide_always: bool,
}

#[derive(Debug, Parser)]
pub struct ConfigArgs {
    /// All arguments are forwarded to `why3find config`; see `why3find config --help` for a list of options.
    #[clap(allow_hyphen_values = true)]
    pub args: Vec<String>,
}

fn check_why3find_json_exists(root: &PathBuf) -> Result<()> {
    let why3find = root.join("why3find.json");
    if why3find.exists() {
        Ok(())
    } else {
        Err(anyhow::anyhow!(
            "{} not found. Perhaps you are in the wrong directory, or you need to run `cargo creusot init`.",
            why3find.display()
        ))
    }
}

fn raw_prove(args: ProveArgs, paths: &Paths) -> Result<()> {
    let mut why3find = Command::new(&paths.why3find);
    why3find.arg("prove");
    if args.ide.ide_on_fail {
        why3find.arg("-i");
    }
    if args.replay {
        why3find.arg("-r");
    }
    // `--ide-always` requires Why3 session files
    if args.why3session || args.ide.ide_always {
        why3find.arg("-s");
    }
    why3find.args(&args.files);
    if let Some(why3_path) = paths.why3.parent() {
        let mut path = why3_path.to_path_buf().into_os_string();
        path.push(":");
        path.push(std::env::var("PATH").unwrap());
        why3find.env("PATH", path);
    }
    why3find
        .env("WHY3CONFIG", &paths.why3_config)
        .status()
        .map_err(|e| anyhow::Error::new(e).context("'why3find prove' failed to launch"))
        .and_then(
            |status| {
                if status.success() { Ok(()) } else { Err(anyhow!("'why3find prove' failed")) }
            },
        )
}

pub fn why3find_prove(mut args: ProveArgs, root: &PathBuf) -> Result<()> {
    // Validate `--ide-always`: it only works with a single Coma file.
    let coma = if !args.ide.ide_always {
        None
    } else if args.files.len() == 1 && args.files[0].extension() == Some(OsStr::new("coma")) {
        Some(args.files[0].clone())
    } else {
        return Err(anyhow!("The flag --ide-always requires exacly one Coma file argument"));
    };
    let paths = creusot_paths()?;
    check_why3find_json_exists(root)?;
    // If there are no file arguments, default to `verif/` to avoid accidentally including random Why3 files elsewhere.
    if args.files.is_empty() {
        args.files.push(root.join(OUTPUT_PREFIX));
    }
    // If the proof fails, we still want to run the IDE if `--ide-always` was set.
    let prove_result = raw_prove(args, &paths);
    if let Some(coma) = coma {
        why3_launcher::run_why3(Why3Mode::Ide, coma, String::new(), paths)?;
    }
    prove_result
}
