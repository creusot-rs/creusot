use crate::tools_versions_urls::*;
use anyhow::{anyhow, bail};
use std::{
    path::{Path, PathBuf},
    process::Command,
};

// ----
// we should only need to update the [Binary] definitions below whenever the
// format of a tool binary releases change (unlikely)

pub const WHY3: Binary = Binary {
    display_name: "Why3",
    binary_name: "why3",
    version: WHY3_VERSION,
    detect_version: detect_why3_version,
};

pub const WHY3FIND: Binary = Binary {
    display_name: "why3find",
    binary_name: "why3find",
    version: WHY3FIND_VERSION,
    detect_version: detect_why3find_version,
};

pub const ALTERGO: Binary = Binary {
    display_name: "Alt-Ergo",
    binary_name: "alt-ergo",
    version: ALTERGO_VERSION,
    detect_version: detect_altergo_version,
};

pub const Z3: Binary = Binary {
    display_name: "Z3",
    binary_name: "z3",
    version: Z3_VERSION,
    detect_version: detect_z3_version,
};

pub const CVC4: Binary = Binary {
    display_name: "CVC4",
    binary_name: "cvc4",
    version: CVC4_VERSION,
    detect_version: detect_cvc4_version,
};

pub const CVC5: Binary = Binary {
    display_name: "CVC5",
    binary_name: "cvc5",
    version: CVC5_VERSION,
    detect_version: detect_cvc5_version,
};

pub const PROVERS: &[Binary] = &[ALTERGO, Z3, CVC4, CVC5];

// ----

#[derive(Clone, Copy)]
pub struct Binary {
    pub display_name: &'static str,
    pub binary_name: &'static str,
    pub version: &'static str,
    detect_version: fn(&Path) -> anyhow::Result<String>,
}

// helpers: external binaries

impl Binary {
    pub fn detect_path(&self) -> Option<PathBuf> {
        use which::which;
        which(self.binary_name).ok()
    }

    pub fn detect_version(&self, path: &Path) -> anyhow::Result<String> {
        (self.detect_version)(path)
    }
}

// helpers: why3

fn detect_why3_version(why3: &Path) -> anyhow::Result<String> {
    let version_full = run(Command::new(&why3).arg("--version"))?;
    match version_full.strip_prefix("Why3 platform, version ") {
        Some(version) => {
            let parts: Vec<_> = version.trim_end().split(|c| c == '.' || c == '+').collect();
            Ok(String::from(&parts[..3].join(".")))
        }
        None => {
            bail!("bad Why3 version: {}", version_full)
        }
    }
}

// helpers: why3find

fn detect_why3find_version(why3find: &Path) -> anyhow::Result<String> {
    let version_full = run(Command::new(&why3find).arg("--version"))?;
    match version_full.strip_prefix("why3find v") {
        Some(version) => {
            let parts: Vec<_> = version.trim_end().split(|c| c == '.' || c == '+').collect();
            Ok(String::from(&parts[..3].join(".")))
        }
        None => bail!("bad Why3find version: {}", version_full),
    }
}

// helpers: alt-ergo

fn detect_altergo_version(altergo: &Path) -> anyhow::Result<String> {
    let version_full = run(Command::new(&altergo).arg("--version"))?;
    let version = version_full.trim_end().strip_prefix("v").map(String::from);
    version.ok_or(anyhow!("bad Altergo version: {}", version_full))
}

// helpers: Z3

// assumes a version string of the form: "Z3 version 4.12.4 - 64 bit"
fn detect_z3_version(z3: &Path) -> anyhow::Result<String> {
    let version_full = run(Command::new(&z3).arg("--version"))?;
    let version = version_full
        .strip_prefix("Z3 version ")
        .and_then(|version| version.split_ascii_whitespace().next().map(String::from));
    version.ok_or(anyhow!("bad Z3 version: {}", version_full))
}

// cvc4

// assumes a version of the form: "This is CVC4 version 1.8 [git HEAD 52479010]\n....."
fn detect_cvc4_version(cvc4: &Path) -> anyhow::Result<String> {
    let version_full = run(Command::new(&cvc4).arg("--version"))?;
    let version = version_full
        .strip_prefix("This is CVC4 version ")
        .and_then(|version| version.split_ascii_whitespace().next().map(String::from));
    version.ok_or(anyhow!("bad CVC4 version: {}", version_full))
}

// cvc5

// assumes a version of the form: "This is cvc5 version 1.0.5 [git ...]\n....."
fn detect_cvc5_version(cvc5: &Path) -> anyhow::Result<String> {
    let version_full = run(Command::new(&cvc5).arg("--version"))?;
    let version = version_full
        .strip_prefix("This is cvc5 version ")
        .and_then(|version| version.split_ascii_whitespace().next().map(String::from));
    version.ok_or(anyhow!("bad CVC5 version: {}", version_full))
}

// Wrapper for Command::output(), error is wrapped in anyhow::Error
fn run(cmd: &mut Command) -> anyhow::Result<String> {
    cmd.output()
        .map_err(|e| {
            if e.kind() == std::io::ErrorKind::NotFound {
                anyhow!("{:?} not found", cmd.get_program())
            } else {
                anyhow!("{:?}: {}", cmd, e)
            }
        })
        .and_then(|output| {
            if output.status.success() {
                Ok(String::from_utf8(output.stdout)?)
            } else {
                let stderr =
                    String::from_utf8(output.stderr).unwrap_or_else(|_| String::from("<stderr>"));
                bail!("{:?} failed: {}\n{}", cmd, output.status, stderr)
            }
        })
}
