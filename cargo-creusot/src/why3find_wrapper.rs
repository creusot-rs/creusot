use anyhow::Result;
use clap::*;
use creusot_setup::{get_why3_config_file, PROVERS};
use std::{
    path::{Path, PathBuf},
    process::{Command, Stdio},
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

fn raw_config(args: &Vec<String>, why3_config_file: &PathBuf) -> Result<()> {
    let mut why3find = Command::new("why3find");
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
        .env("WHY3CONFIG", &why3_config_file)
        .stdout(Stdio::inherit())
        .stderr(Stdio::inherit())
        .status()
        .map_err(|e| anyhow::Error::new(e).context("why3find config failed"))
        .map(|_| ())
}

fn raw_prove(args: ProveArgs, why3_config_file: &PathBuf) -> Result<()> {
    let mut why3find = Command::new("why3find");
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
    why3find
        .env("WHY3CONFIG", &why3_config_file)
        .stdout(Stdio::inherit())
        .stderr(Stdio::inherit())
        .status()
        .map_err(|e| anyhow::Error::new(e).context("why3find prove failed"))
        .map(|_| ())
}

pub fn why3find_config(args: ConfigArgs) -> Result<()> {
    let paths = get_why3_config_file()?;
    raw_config(&args.args, &paths)
}

pub fn why3find_prove(args: ProveArgs) -> Result<()> {
    let paths = get_why3_config_file()?;
    if !why3find_json_exists() {
        return Err(anyhow::anyhow!("why3find.json not found. Perhaps you are in the wrong directory, or you need to run `cargo creusot config`."));
    }
    raw_prove(args, &paths)
}
