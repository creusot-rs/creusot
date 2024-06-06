use std::{
    path::{Path, PathBuf},
    process::Command,
};

use super::helpers::Result;
use anyhow::anyhow;
use include_dir::{include_dir, Dir};

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
pub struct Why3Launcher {
    mode: Why3Mode,
    why3_path: Option<PathBuf>,
    config_file: Option<PathBuf>,
    args: Option<String>,
    output_file: PathBuf,
}

impl Why3Launcher {
    pub fn new(
        mode: Why3Mode,
        why3_path: Option<PathBuf>,
        config_file: Option<PathBuf>,
        args: Option<String>,
        output_file: PathBuf,
    ) -> Self {
        Self { mode, why3_path, config_file, args, output_file }
    }

    pub fn make(&self, temp_dir: &Path) -> Result<Command> {
        let mut cmd_output_file = self.output_file.clone();

        //
        if self.mode == Why3Mode::Replay {
            cmd_output_file.set_extension("");
        }

        let mode = self.mode.to_string();
        let mut prelude_dir: PathBuf = temp_dir.into();
        prelude_dir.push("prelude");
        std::fs::create_dir(&prelude_dir)?;

        PRELUDE
            .extract(prelude_dir)
            .expect("can't launch why3, could extract prelude into temp dir");

        let mut command =
            if let Some(p) = &self.why3_path { Command::new(p) } else { Command::new("why3") };
        command
            .args([
                "--warn-off=unused_variable",
                "--warn-off=clone_not_abstract",
                "--warn-off=axiom_abstract",
                &mode,
                "-L",
            ])
            .arg(temp_dir.as_os_str())
            .arg(&cmd_output_file);


        if let Some(cfg) = &self.config_file {
            command.arg("-C").arg(cfg);
        }
        if let Some(args) = &self.args {
            if !args.is_empty() {
                command.args(args.split_ascii_whitespace());
            }
        }

        Ok(command)
    }
}

pub struct Why3LauncherBuilder {
    mode: Why3Mode,
    why3_path: Option<PathBuf>,
    config_file: Option<PathBuf>,
    args: Option<String>,
    output_file: Option<PathBuf>,
}

impl Why3LauncherBuilder {
    pub fn new() -> Self {
        Self {
            mode: Why3Mode::Ide,
            why3_path: None,
            config_file: None,
            args: None,
            output_file: None,
        }
    }

    pub fn mode(&mut self, m: Why3Mode) -> &mut Self {
        self.mode = m;
        self
    }

    pub fn why3_path(&mut self, p: PathBuf) -> &mut Self {
        self.why3_path = Some(p);
        self
    }

    pub fn config_file(&mut self, p: PathBuf) -> &mut Self {
        self.config_file = Some(p);
        self
    }

    pub fn args(&mut self, a: String) -> &mut Self {
        self.args = Some(a);
        self
    }

    pub fn output_file(&mut self, p: PathBuf) -> &mut Self {
        self.output_file = Some(p);
        self
    }

    pub fn build(self) -> Result<Why3Launcher> {
        let Some(coma_file) = self.output_file else {
            return Err(anyhow!("can't launch why3, no coma_file specify"));
        };

        Ok(Why3Launcher::new(self.mode, self.why3_path, self.config_file, self.args, coma_file))
    }
}
