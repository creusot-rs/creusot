use anyhow::{Result, anyhow};
use clap::*;
use creusot_setup::{Paths, creusot_paths};
use std::{path::PathBuf, process::Command};

use crate::OUTPUT_PREFIX;

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

fn raw_prove(args: ProveArgs, paths: &Paths) -> Result<()> {
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
    let paths = creusot_paths()?;
    check_why3find_json_exists(root)?;
    // If there are no file arguments, default to `verif/` to avoid accidentally including random Why3 files elsewhere.
    if args.files.is_empty() {
        args.files.push(root.join(OUTPUT_PREFIX));
    }
    raw_prove(args, &paths)
}

/// Given `file.coma`, create `file/why3session.xml` from `file/proof.json`.
pub fn try_create_why3session(coma: &PathBuf, replay: bool, paths: &Paths) -> Result<()> {
    raw_prove(
        ProveArgs { ide: false, replay, why3session: true, files: vec![coma.clone()] },
        paths,
    )
}
