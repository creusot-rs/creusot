use std::{
    path::{Path, PathBuf},
    process::Command,
};

use super::helpers::Result;
use include_dir::{Dir, include_dir};

static PRELUDE: Dir<'static> = include_dir!("$CARGO_MANIFEST_DIR/../prelude");

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
    pub config_file: PathBuf,
    pub args: String,
    pub include_dir: Option<PathBuf>,
    pub coma_files: Vec<PathBuf>,
}

impl Why3Launcher {
    pub fn make(&self, temp_dir: &Path) -> Result<Command> {
        let mode = self.mode.to_string();
        let mut prelude_dir: PathBuf = temp_dir.into();
        prelude_dir.push("prelude");
        std::fs::create_dir(&prelude_dir)?;

        PRELUDE
            .extract(prelude_dir)
            .expect("can't launch why3, could extract prelude into temp dir");

        let mut command = Command::new(&self.why3_path);
        command
            .args([
                "--warn-off=unused_variable",
                "--warn-off=clone_not_abstract",
                "--warn-off=axiom_abstract",
                "--debug=coma_no_trivial",
                &mode,
                "-L",
            ])
            .arg(temp_dir.as_os_str());

        match &self.include_dir {
            Some(dir) => {
                command.arg("-L").arg(dir.as_os_str());
            }
            None => {}
        }

        for file in &self.coma_files {
            command.arg(&file);
        }

        command.arg("-C").arg(&self.config_file);

        if !self.args.is_empty() {
            command.args(self.args.split_ascii_whitespace());
        }

        Ok(command)
    }
}
