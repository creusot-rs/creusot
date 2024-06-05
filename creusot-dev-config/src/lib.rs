use std::{path::PathBuf, process::Command};

/// Helper library encapsulating the logic for looking up creusot's config and
/// calling why3 in development workflows. This is used in particular by the
/// testsuite.

pub struct Paths {
    pub why3: PathBuf,
    pub why3_config: PathBuf,
}

/// Fails if the config could not be loaded
pub fn paths() -> anyhow::Result<Paths> {
    let paths = creusot_setup::status_for_creusot()?;
    Ok(Paths { why3: paths.why3_path, why3_config: paths.why3_config })
}

/// Returns a command to invoke why3 (passing it the path to its configuration
/// file if needed).
/// Fails if the config could not be loaded
pub fn why3_command() -> anyhow::Result<Command> {
    let p = paths()?;
    let mut cmd = Command::new(p.why3.clone());
    cmd.arg("-C").arg(p.why3_config);
    Ok(cmd)
}
