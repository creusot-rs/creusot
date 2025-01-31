use anyhow::{anyhow, Result};
use clap::*;
use creusot_setup::{creusot_paths, Paths, PROVERS};
use std::{
    path::{Path, PathBuf},
    process::Command,
    str::FromStr,
};

#[derive(Debug, Parser)]
pub struct ProveArgs {
    /// Run Why3 IDE on next unproved goal.
    #[clap(short = 'i', default_value_t = false, action = clap::ArgAction::SetTrue)]
    pub ide: bool,
    /// Files to prove; default to everything in `verif/`.
    pub files: Vec<PathBuf>,
}

#[derive(Debug, Parser)]
pub struct ConfigArgs {
    /// All arguments are forwarded to `why3find config`; see `why3find config --help` for a list of options.
    #[clap(allow_hyphen_values = true)]
    pub args: Vec<String>,
}

fn why3find_json_exists() -> bool {
    Path::new("why3find.json").exists()
}

fn raw_config(args: &Vec<String>, paths: &Paths) -> Result<()> {
    let mut why3find = Command::new(&paths.why3find);
    why3find
        .arg("config")
        .arg("--quiet")
        .arg("--why3-warn-off")
        .arg("unused_variable,axiom_abstract")
        .arg("--package")
        .arg("prelude");
    for prover in PROVERS {
        why3find.arg("--prover").arg(format!("+{}", prover.bin.binary_name));
    }
    for arg in args {
        why3find.arg(arg);
    }
    why3find
        .env("WHY3CONFIG", &paths.why3_config)
        .status()
        .map_err(|e| anyhow::Error::new(e).context("'why3find config' failed to launch"))
        .and_then(
            |status| {
                if status.success() {
                    Ok(())
                } else {
                    Err(anyhow!("'why3find config' failed"))
                }
            },
        )
}

fn raw_prove(args: ProveArgs, paths: &Paths) -> Result<()> {
    let mut why3find = Command::new(&paths.why3find);
    why3find.arg("prove");
    if args.ide {
        why3find.arg("-i");
    }
    // If there are no file arguments, default to `verif/` to avoid accidentally including random Why3 files elsewhere.
    let files =
        if args.files.len() == 0 { vec![PathBuf::from_str("verif").unwrap()] } else { args.files };
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
                if status.success() {
                    Ok(())
                } else {
                    Err(anyhow!("'why3find prove' failed"))
                }
            },
        )
}

pub fn why3find_config(args: ConfigArgs) -> Result<()> {
    let paths = creusot_paths()?;
    raw_config(&args.args, &paths)
}

pub fn why3find_prove(args: ProveArgs) -> Result<()> {
    let paths = creusot_paths()?;
    if !why3find_json_exists() {
        return Err(anyhow::anyhow!("why3find.json not found. Perhaps you are in the wrong directory, or you need to run `cargo creusot config`."));
    }
    raw_prove(args, &paths)
}
