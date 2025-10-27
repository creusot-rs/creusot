use anyhow::{Context as _, Result};
use creusot_setup::{CreusotPaths, generate_why3_conf};
use std::{
    fs,
    path::{Path, PathBuf},
    process::Command,
};

#[derive(Copy, Clone, Debug, PartialEq)]
pub enum Why3Mode {
    Ide,
    Replay,
}

impl std::fmt::Display for Why3Mode {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Why3Mode::Ide => f.write_str("ide"),
            Why3Mode::Replay => f.write_str("replay"),
        }
    }
}

pub(crate) fn run_why3(
    mode: Why3Mode,
    coma_file: PathBuf,
    args: String,
    paths: &CreusotPaths,
) -> Result<()> {
    check_why3_conf_exists(paths)?;
    let prelude = std::ffi::OsString::from(String::from_utf8(
        Command::new(paths.why3find()).arg("where").output()?.stdout,
    )?);
    let mut why3 = Command::new(paths.why3());
    why3.args([
        "--warn-off=unused_variable",
        "--warn-off=clone_not_abstract",
        "--warn-off=axiom_abstract",
        "--debug=coma_no_trivial",
        "-L",
    ])
    .arg(&prelude)
    .arg(mode.to_string())
    .arg(coma_file)
    .arg("-C")
    .arg(paths.why3_conf());
    if !args.is_empty() {
        why3.args(args.split_ascii_whitespace());
    }
    why3.status().context("could not run why3")?;
    Ok(())
}

pub(crate) fn check_why3_conf_exists(paths: &CreusotPaths) -> Result<()> {
    if older(&paths.why3_conf(), &paths.data_dir()) {
        generate_why3_conf(paths, None)?;
    }
    Ok(())
}

// `true` if `older` does not exist or is older than `newer`.
pub fn older(older: &Path, newer: &Path) -> bool {
    let Ok(older_meta) = fs::metadata(older) else { return true };
    let Ok(newer_meta) = fs::metadata(newer) else { return false };
    let (Ok(older_time), Ok(newer_time)) = (older_meta.modified(), newer_meta.modified()) else {
        return false;
    };
    older_time < newer_time
}
