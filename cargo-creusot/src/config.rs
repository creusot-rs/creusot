use std::{
    ffi::OsStr,
    fs,
    io::Write as _,
    os::unix::ffi::OsStrExt as _,
    path::{Path, PathBuf},
};

use anyhow::{Context as _, Result, bail};
use cargo_metadata::semver::Version;
use clap::Parser;
use toml_edit::{DocumentMut, InlineTable, TableLike};

/// Only remember the version string at compile-time
pub(crate) const CREUSOT_STD_VERSION: &str = env!("CARGO_PKG_VERSION");

#[derive(Debug, Parser)]
pub struct ConfigArgs {
    /// Update the configuration (default is to only check it)
    #[clap(long)]
    update: bool,
    /// Act on `$CARGO_HOME/config.toml` instead of the current project's `.cargo/config.toml`.
    /// The global config should not patch `creusot-std` (it used to be the recommended setup),
    /// so `--update --global` removes that patch.
    #[clap(long)]
    global: bool,
    /// Path to local Creusot repository (only for dev versions of Creusot)
    #[clap(long, env = "CREUSOT_PATH")]
    pub creusot_path: Option<PathBuf>,
}

pub fn config(args: ConfigArgs) -> Result<()> {
    if args.global {
        let cargo_config = cargo_home().join("config.toml");
        let fix = "cargo creusot config --update --global";
        return sync_patch(&cargo_config, None, args.update, fix);
    }
    let root = workspace_root()?;
    let desired = project_creusot_std_path(&root, args.creusot_path)?;
    let fix = "cargo creusot config --update";
    sync_patch(&root.join(".cargo/config.toml"), desired.as_deref(), args.update, fix)?;
    if !args.update {
        warn_global_patch()?;
    }
    Ok(())
}

/// Path to the local `creusot-std` if this is a dev version of Creusot, `None` for released versions.
pub(crate) fn dev_creusot_std_path(creusot_path: Option<PathBuf>) -> Result<Option<PathBuf>> {
    let self_version = Version::parse(CREUSOT_STD_VERSION)?;
    if self_version.pre.is_empty() {
        return Ok(None);
    }
    let creusot_path = creusot_path
        .or_else(|| std::env::var_os("CREUSOT_PATH").map(PathBuf::from))
        .unwrap_or_else(creusot_source_path);
    Ok(Some(creusot_path.join("creusot-std")))
}

/// Path that the project at `root` should use for `creusot-std` (`None` if it should use crates.io).
/// The Creusot repository itself needs no patch.
fn project_creusot_std_path(root: &Path, creusot_path: Option<PathBuf>) -> Result<Option<PathBuf>> {
    let Some(creusot_std) = dev_creusot_std_path(creusot_path)? else { return Ok(None) };
    if let Some(repo) = creusot_std.parent()
        && let (Ok(repo), Ok(root)) = (repo.canonicalize(), root.canonicalize())
        && root.starts_with(repo)
    {
        return Ok(None);
    }
    Ok(Some(creusot_std))
}

/// Argument for `cargo --config` to patch `creusot-std` with a local path.
pub(crate) fn patch_config_arg(creusot_std: &Path) -> String {
    let path = toml_edit::Value::from(creusot_std.to_string_lossy().as_ref());
    format!("patch.crates-io.creusot-std.path={}", path.to_string().trim())
}

/// Write `[patch.crates-io.creusot-std]` in `<root>/.cargo/config.toml`
/// for dev versions of Creusot (or remove it for released versions).
pub(crate) fn update_project_config(root: &Path) -> Result<()> {
    let desired = project_creusot_std_path(root, None)?;
    sync_patch(&root.join(".cargo/config.toml"), desired.as_deref(), true, "")
}

/// Print a warning if `$CARGO_HOME/config.toml` patches `creusot-std`.
fn warn_global_patch() -> Result<()> {
    let cargo_config = cargo_home().join("config.toml");
    let (config, _) = read_config(&cargo_config)?;
    if get_patch(&config).is_some() {
        println!(
            "In {}: found patch for creusot-std, which affects all your Rust projects.\nRun `cargo creusot config --update --global` to remove it.",
            cargo_config.display()
        );
    }
    Ok(())
}

fn cargo_home() -> PathBuf {
    match std::env::var_os("CARGO_HOME") {
        None => PathBuf::from(std::env::var_os("HOME").unwrap()).join(".cargo"),
        Some(p) => PathBuf::from(p),
    }
}

/// Root of the current Cargo workspace.
/// Uses `cargo locate-project` which, unlike `cargo metadata`,
/// does not need to resolve dependencies (which fails if the patch is missing).
pub(crate) fn workspace_root() -> Result<PathBuf> {
    let cargo = std::env::var_os("CARGO").unwrap_or_else(|| "cargo".into());
    let output = std::process::Command::new(cargo)
        .args(["locate-project", "--workspace", "--message-format", "plain"])
        .output()
        .context("could not run cargo")?;
    if !output.status.success() {
        bail!(
            "Not in a Cargo project: {}(Use --global to check $CARGO_HOME/config.toml)",
            String::from_utf8_lossy(&output.stderr)
        )
    }
    let manifest = PathBuf::from(OsStr::from_bytes(output.stdout.trim_ascii_end()));
    Ok(manifest.parent().unwrap().to_path_buf())
}

/// Read a TOML file. Also return whether it exists.
fn read_config(path: &Path) -> Result<(DocumentMut, bool)> {
    match fs::read_to_string(path) {
        Ok(s) => Ok((s.parse::<DocumentMut>()?, true)),
        Err(e) if e.kind() == std::io::ErrorKind::NotFound => Ok((DocumentMut::new(), false)),
        Err(e) => Err(e).with_context(|| format!("Failed to read {}", path.display())),
    }
}

fn get_patch(config: &DocumentMut) -> Option<&toml_edit::Item> {
    config.get("patch")?.get("crates-io")?.get("creusot-std")
}

/// Check or update the `[patch.crates-io.creusot-std]` entry in the Cargo config file `cargo_config`.
/// `desired` is the path that `creusot-std` should be patched with, or `None` if there should be no patch.
/// `fix` is the command to suggest when checking finds a problem.
fn sync_patch(cargo_config: &Path, desired: Option<&Path>, update: bool, fix: &str) -> Result<()> {
    let (mut config, exists) = read_config(cargo_config)?;
    let current = get_patch(&config).map(|p| p.get("path").and_then(|p| p.as_str()));
    let up_to_date = match (current, desired) {
        (None, None) => true,
        (Some(Some(path)), Some(desired)) => OsStr::from_bytes(path.as_bytes()) == desired,
        _ => false,
    };
    if up_to_date {
        if !update {
            println!("No problems found in {}.", cargo_config.display());
        }
        return Ok(());
    }
    if !update {
        let problem = match (current, desired) {
            (Some(_), None) => "found patch for creusot-std, which should be removed".to_string(),
            (None, Some(_)) => format!("no path found for creusot-std {CREUSOT_STD_VERSION}"),
            _ => format!("path for creusot-std {CREUSOT_STD_VERSION} may be out of date"),
        };
        println!("In {}: {problem}.\nRun `{fix}`.", cargo_config.display());
        return Ok(());
    }
    let Some(patch) = implicit_table(config.as_table_mut(), "patch").as_table_like_mut() else {
        bail!("In {}: [patch] is not a table", cargo_config.display())
    };
    let Some(crates_io) = implicit_table(patch, "crates-io").as_table_like_mut() else {
        bail!("In {}: [patch.crates-io] is not a table", cargo_config.display())
    };
    if let Some(desired) = desired {
        let creusot_std =
            crates_io.entry("creusot-std").or_insert_with(|| InlineTable::new().into());
        creusot_std["path"] = desired.to_str().context("non-UTF-8 path")?.into();
    } else {
        let _ = crates_io.remove("creusot-std");
        if crates_io.is_empty() {
            patch.remove("crates-io");
        }
        if patch.is_empty() {
            config.remove("patch");
        }
        if config.is_empty() {
            if exists {
                println!("Removing empty {}", cargo_config.display());
                fs::remove_file(cargo_config)?;
                // Remove `.cargo` if it is now empty (fails harmlessly otherwise)
                let _ = fs::remove_dir(cargo_config.parent().unwrap());
            }
            return Ok(());
        }
    }
    println!("Updating {}", cargo_config.display());
    fs::create_dir_all(cargo_config.parent().unwrap())?;
    fs::write(cargo_config, config.to_string())
        .with_context(|| format!("Failed to write {}", cargo_config.display()))
}

/// The hard-coded path to the source of creusot-std
/// Note: this is meaningless in nix. The nix config will set CREUSOT_PATH
/// so this should not be reachable.
fn creusot_source_path() -> PathBuf {
    // This must be the dev version of `cargo-creusot`.
    // It should have been installed from source and `creusot-std`
    // should be available next to its source.
    let mut path = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    path.pop();
    path
}

/// Do not overwrite existing file.
/// Warn if writing fails, then return.
pub(crate) fn write(path: impl AsRef<Path>, contents: &str) {
    let path = path.as_ref();
    fs::File::create_new(path)
        .and_then(|mut file| file.write_all(contents.as_ref()))
        .unwrap_or_else(|e| {
            if e.kind() == std::io::ErrorKind::AlreadyExists {
                eprintln!("File '{}' already exists. (Skipped)", path.display());
            } else {
                eprintln!("Could not write to '{}': {} (Skipped)", path.display(), e);
            }
        });
}

/// Get the value for the key if it exists.
/// If the key doesn't exist, insert a `Table` and mark it implicit.
///
/// We don't just use `Index` (`toml[key]`) because it creates an
/// `InlineTable` instead of a `Table`.
/// And we call `set_implicit` because otherwise we would get an empty `[patch]`
/// table next to `[patch.crates-io]` to appear in our generated toml file.
pub(crate) fn implicit_table<'a, T: TableLike + ?Sized>(
    toml: &'a mut T,
    key: &'a str,
) -> &'a mut toml_edit::Item {
    toml.entry(key).or_insert_with(|| {
        let mut table = toml_edit::Table::new();
        table.set_implicit(true);
        table.into()
    })
}
