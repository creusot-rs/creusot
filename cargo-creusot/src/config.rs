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
    /// Update `.cargo/config.toml` (default is to only check it)
    #[clap(long)]
    update: bool,
    /// Path to local creusot-std relative to the generated Cargo.toml
    #[clap(long, env = "CREUSOT_PATH")]
    pub creusot_path: Option<PathBuf>,
}

pub fn config(args: ConfigArgs) -> Result<()> {
    let self_version = Version::parse(CREUSOT_STD_VERSION)?;
    let creusot_path = if self_version.pre.is_empty() {
        None
    } else {
        args.creusot_path.or_else(|| Some(creusot_source_path()))
    };
    let home = PathBuf::from(std::env::var_os("HOME").unwrap());
    let cargo_config = home.join(".cargo/config.toml");
    let mut config_does_not_exist = false;
    let mut config = fs::read_to_string(&cargo_config)
        .or_else(|e| {
            if e.kind() == std::io::ErrorKind::NotFound {
                config_does_not_exist = true;
                Ok(Default::default())
            } else {
                bail!(e)
            }
        })?
        .parse::<DocumentMut>()?;
    let Some(patch) = implicit_table(config.as_table_mut(), "patch").as_table_like_mut() else {
        bail!("[patch] is not a table")
    };
    let Some(crates_io) = implicit_table(patch, "crates-io").as_table_like_mut() else {
        bail!("[patch.crates-io] is not a table")
    };
    if args.update {
        if let Some(creusot_path) = creusot_path {
            let creusot_std =
                crates_io.entry("creusot-std").or_insert_with(|| InlineTable::new().into());
            if let Some(path) = creusot_std.get("path")
                && let Some(path) = path.as_str()
                && OsStr::from_bytes(path.as_bytes())
                    == creusot_path.join("creusot-std").as_os_str()
            {
                return Ok(());
            }
            creusot_std["path"] = creusot_path.join("creusot-std").to_str().unwrap().into();
        } else {
            if config_does_not_exist {
                return Ok(());
            }
            let _ = crates_io.remove("creusot-std");
            if crates_io.is_empty() {
                patch.remove("crates-io");
            }
            if patch.is_empty() {
                config.remove("patch");
            }
            if config.is_empty() {
                println!("Removing empty {}", cargo_config.display());
                fs::remove_file(cargo_config)?;
                return Ok(());
            }
        }
        println!("Updating {}", cargo_config.display());
        fs::write(&cargo_config, config.to_string())
            .with_context(|| format!("Failed to write {}", cargo_config.display()))?;
    } else {
        if let Some(creusot_path) = creusot_path {
            if config_does_not_exist {
                println!(
                    "No {} needed to set path to creusot-std {CREUSOT_STD_VERSION}. Run `cargo creusot config --update`.",
                    cargo_config.display()
                );
            } else if let Some(creusot_std) = crates_io.get("creusot-std")
                && let Some(path) = creusot_std.get("path")
                && let Some(path) = path.as_str()
            {
                if OsStr::from_bytes(path.as_bytes())
                    != creusot_path.join("creusot-std").as_os_str()
                {
                    println!(
                        "In {}: path for creusot-std {CREUSOT_STD_VERSION} may be out of date. Run `cargo creusot config --update.",
                        cargo_config.display()
                    )
                } else {
                    println!("No problems found.")
                }
            } else {
                println!(
                    "In {}: no path found for creusot-std {CREUSOT_STD_VERSION}.\nRun `cargo creusot config --update`.",
                    cargo_config.display()
                )
            };
        } else {
            if let Some(_) = crates_io.get("creusot-std") {
                println!(
                    "In {}: found patch for creusot-std, but you are using a released version of Creusot ({CREUSOT_STD_VERSION}).\nRun `cargo creusot config --update` to remove it.",
                    cargo_config.display()
                );
            } else {
                println!("No problems found.")
            }
        }
    }
    Ok(())
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
