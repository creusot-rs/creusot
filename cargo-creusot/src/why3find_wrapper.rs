use anyhow::{Result, anyhow};
use clap::*;
use creusot_setup::{Paths, creusot_paths};
use std::{path::PathBuf, process::Command};

#[derive(Debug, Parser)]
pub struct ProveArgs {
    /// Run Why3 IDE on next unproved goal.
    #[clap(long, short = 'i')]
    pub ide: bool,
    /// Replay proofs only, no update.
    #[clap(long)]
    pub replay: bool,
    /// Generate Why3 sessions for why3 ide.
    #[clap(long)]
    pub why3session: bool,
    /// Files to prove; default to everything in `verif/`.
    pub files: Vec<PathBuf>,
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

fn raw_prove(args: ProveArgs, paths: &Paths, root: &PathBuf) -> Result<()> {
    let mut why3find = Command::new(&paths.why3find);
    why3find.arg("prove");
    if args.ide {
        why3find.arg("-i");
    }
    if args.replay {
        why3find.arg("-r");
    }
    if args.why3session {
        why3find.arg("-s");
    }
    // If there are no file arguments, default to `verif/` to avoid accidentally including random Why3 files elsewhere.
    let files = if args.files.len() == 0 { vec![root.join("verif")] } else { args.files };
    for file in files {
        why3find.arg(file);
    }
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

pub fn why3find_prove(args: ProveArgs, root: &PathBuf) -> Result<()> {
    let paths = creusot_paths()?;
    check_why3find_json_exists(root)?;
    raw_prove(args, &paths, root)
}
