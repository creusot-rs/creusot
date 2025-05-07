use anyhow::{Context as _, Result};
use creusot_setup::Paths;
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

#[derive(Debug)]
pub(crate) struct Why3Launcher {
    pub mode: Why3Mode,
    pub why3_path: PathBuf,
    pub why3find_path: PathBuf,
    pub config_file: PathBuf,
    pub args: String,
    pub coma_file: PathBuf,
}

impl Why3Launcher {
    pub fn make(&self) -> Result<Command> {
        let mode = self.mode.to_string();
        let mut command = Command::new(&self.why3_path);
        // Assuming that why3find is in an Opam switch `_opam/bin/why3find`,
        // we guess that the creusot prelude is in `_opam/lib/why3find/packages/creusot`.
        let mut prelude = self.why3find_path.clone();
        prelude.pop();
        prelude.pop();
        prelude.push("lib/why3find/packages/creusot");
        command
            .args([
                "--warn-off=unused_variable",
                "--warn-off=clone_not_abstract",
                "--warn-off=axiom_abstract",
                "--debug=coma_no_trivial",
                &mode,
                "-L",
            ])
            .arg(&prelude)
            .arg(&self.coma_file)
            .arg("-C")
            .arg(&self.config_file);

        if !self.args.is_empty() {
            command.args(self.args.split_ascii_whitespace());
        }

        Ok(command)
    }
}

pub(crate) fn run_why3(
    mode: Why3Mode,
    coma_file: PathBuf,
    args: String,
    paths: Paths,
) -> Result<()> {
    let why3 = Why3Launcher {
        why3_path: paths.why3,
        why3find_path: paths.why3find,
        config_file: paths.why3_config,
        mode,
        coma_file,
        args,
    };
    let mut command = why3.make()?;
    command.status().context("could not run why3")?;
    Ok(())
}
