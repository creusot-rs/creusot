use std::{path::PathBuf, process::Command};

/// Helper library encapsulating the logic for looking up creusot's config and
/// calling why3 in development workflows. This is used in particular by the
/// testsuite.

/// We look for configuration specifying Why3's path and configuration in the
/// following places:
/// - in the .creusot-config directory at the root of the git repo, if it exists
/// - otherwise, in the global config repository used by creusot setup

pub fn custom_config_dir() -> Option<PathBuf> {
    let local_config = PathBuf::from("../.creusot-config");
    if local_config.is_dir() {
        Some(std::fs::canonicalize(local_config).unwrap())
    } else {
        None
    }
}

pub struct Paths {
    pub why3: PathBuf,
    pub why3_config: Option<PathBuf>,
}

/// Fails if the config could not be loaded
pub fn paths() -> anyhow::Result<Paths> {
    let custom_config_dir = custom_config_dir();
    let paths = creusot_setup::status_for_creusot(&custom_config_dir)?;
    Ok(Paths { why3: paths.why3_path, why3_config: paths.why3_config })
}

/// Returns a command to invoke why3 (passing it the path to its configuration
/// file if needed).
/// Fails if the config could not be loaded
pub fn why3_command() -> anyhow::Result<Command> {
    let p = paths()?;
    let mut cmd = Command::new(p.why3.clone());
    if let Some(ref config) = p.why3_config {
        cmd.arg("-C").arg(config);
    }
    Ok(cmd)
}
