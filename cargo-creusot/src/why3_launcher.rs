use anyhow::{Context as _, Result};
use creusot_setup::CreusotPaths;
use std::{path::PathBuf, process::Command};

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
    creusot_setup::update_why3_conf(paths, None)?;
    let mut why3 = Command::new(paths.why3());
    // Add Creusot bin path to PATH to find solvers
    // Still keep the old paths for other binaries that why3 ide may use (like the editor).
    let mut path = paths.bin().to_path_buf().into_os_string();
    path.push(":");
    path.push(std::env::var("PATH").unwrap());
    why3.env("PATH", path);
    why3.args([
        "--warn-off=unused_variable",
        "--warn-off=clone_not_abstract",
        "--warn-off=axiom_abstract",
        "--debug=coma_no_trivial",
        "-L",
    ])
    .arg(paths.why3find_libs().join("packages/creusot"))
    .arg(mode.to_string())
    .arg(coma_file)
    .arg("-C")
    .arg(paths.user_why3_conf())
    .arg("--extra-config")
    .arg(paths.creusot_why3_conf());
    if !args.is_empty() {
        why3.args(args.split_ascii_whitespace());
    }
    why3.status().context("could not run why3")?;
    Ok(())
}
