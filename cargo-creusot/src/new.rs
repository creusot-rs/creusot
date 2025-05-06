use anyhow::Result;
use cargo_metadata::semver::Version;
use clap::Parser;
use creusot_setup::creusot_paths;
use std::{
    fs,
    io::Write,
    path::{Path, PathBuf},
};

use crate::helpers::{CREUSOT_CONTRACTS_VERSION, creusot_contracts_path};

#[derive(Debug, Parser)]
pub struct NewArgs {
    /// Package name
    pub name: String,
    #[clap(flatten)]
    pub args: NewInitArgs,
}

#[derive(Debug, Parser)]
pub struct InitArgs {
    /// Package name (default: name of the current directory)
    pub name: Option<String>,
    #[clap(flatten)]
    pub args: NewInitArgs,
}

/// Shared arguments for `new` and `init`
#[derive(Debug, Parser)]
pub struct NewInitArgs {
    /// Create main.rs
    #[clap(long)]
    pub main: bool,
    /// Create test directory
    #[clap(long)]
    pub tests: bool,
    /// Path to local creusot-contracts relative to the generated Cargo.toml
    #[clap(long)]
    pub creusot_contracts: Option<String>,
}

fn cargo_template(name: &str) -> String {
    let version = Version::parse(CREUSOT_CONTRACTS_VERSION).unwrap();
    let patch = if version.pre.is_empty() {
        "".to_string()
    } else {
        format!(
            r#"
[patch.crates-io]
creusot-contracts = {{ path = "{}" }}
"#,
            creusot_contracts_path().display()
        )
    };
    format!(
        r#"[package]
name = "{name}"
version = "0.1.0"
edition = "2024"

[dependencies]
creusot-contracts = "{CREUSOT_CONTRACTS_VERSION}"

[lints.rust]
unexpected_cfgs = {{ level = "warn", check-cfg = ['cfg(creusot)'] }}
{patch}"#
    )
}

fn bin_template(name: &str) -> String {
    let name = name.replace("-", "_");
    format!(
        r#"#[allow(unused_imports)]
use creusot_contracts::*;
use {name}::*;

fn main() {{
    assert!(add_one(2) == 3);
    println!("Hello, world!");
}}
"#
    )
}

const TEST_TEMPLATE: &str = r#"#[allow(unused_imports)]
use creusot_contracts::*;

#[test]
fn it_works() {
    assert_eq!(2 + 2, 4);
}
"#;

const LIB_TEMPLATE: &str = r#"use creusot_contracts::*;

#[requires(a@ < i64::MAX@)]
#[ensures(result@ == a@ + 1)]
pub fn add_one(a: i64) -> i64 {
    a + 1
}
"#;

pub fn new(args: NewArgs) -> Result<()> {
    validate_name(&args.name)?;
    fs::create_dir(&args.name).map_err(|e| {
        if e.kind() == std::io::ErrorKind::AlreadyExists {
            anyhow::anyhow!("Directory '{}' already exists", args.name)
        } else {
            e.into()
        }
    })?;
    std::env::set_current_dir(&args.name)?;
    create_project(args.name, args.args)
}

pub fn init(args: InitArgs) -> Result<()> {
    let name = match args.name {
        None => {
            // Use name of the current directory
            let current_dir = std::env::current_dir()?;
            current_dir
                .file_name()
                .and_then(|name| name.to_str())
                .ok_or_else(|| anyhow::anyhow!("Could not determine project name"))?
                .to_string()
        }
        Some(name) => name,
    };
    validate_name(&name)?;
    create_project(name, args.args)
}

pub fn create_project(name: String, args: NewInitArgs) -> Result<()> {
    let paths = creusot_paths()?;
    let cargo_toml = Path::new("Cargo.toml");
    if cargo_toml.exists() {
        patch_dep(cargo_toml)?;
    } else {
        write(cargo_toml, &cargo_template(&name));
        if args.tests {
            fs::create_dir_all("tests")?;
            write("tests/test.rs", TEST_TEMPLATE);
        }
        fs::create_dir_all("src")?;
        if args.main {
            write("src/main.rs", &bin_template(&name));
        }
        write("src/lib.rs", LIB_TEMPLATE);
    }
    if let Some(parent_cargo_toml) = find_parent_cargo_toml() {
        eprintln!(
            "Info: It seems that you are in a workspace (found {}), so no why3find.json will be created in the current directory.",
            parent_cargo_toml.display()
        );
    } else {
        let why3find_json = paths.config_dir.join("why3find.json");
        copy(&why3find_json, "why3find.json");
    }
    Ok(())
}

fn find_parent_cargo_toml() -> Option<PathBuf> {
    let mut path = std::env::current_dir().ok()?;
    while path.pop() {
        let cargo_toml = path.join("Cargo.toml");
        if cargo_toml.exists() {
            return Some(cargo_toml);
        }
    }
    None
}

fn validate_name(name: &str) -> Result<()> {
    if !name.chars().all(|c| c.is_ascii_alphanumeric() || c == '-' || c == '_') {
        return Err(anyhow::anyhow!(
            "Invalid name {name}, must contain only 'a-z', 'A-Z', '0-9', '-', or '_'",
        ));
    }
    Ok(())
}

/// Do not overwrite existing file.
/// Warn if writing fails, then return.
fn write(path: impl AsRef<Path>, contents: &str) {
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

/// Do not overwrite existing file.
fn copy(src: impl AsRef<Path>, dst: impl AsRef<Path>) {
    let src = src.as_ref();
    let dst = dst.as_ref();
    if dst.exists() {
        return;
    }
    fs::copy(src, dst).unwrap();
}

/// Add or update creusot-contracts in Cargo.toml:
///
/// ```toml
/// [dependencies]
/// creusot-contracts = "X.Y.Z"
///
/// [patch.crates-io]
/// creusot-contracts = { path = "/path/to/creusot-contracts" }  # Only for dev versions
/// ```
fn patch_dep(cargo_toml_path: impl AsRef<Path>) -> Result<()> {
    let cargo_toml_path = cargo_toml_path.as_ref();
    let self_version = Version::parse(CREUSOT_CONTRACTS_VERSION)?;
    let cargo_toml = std::fs::read_to_string(cargo_toml_path)?;
    let mut cargo_toml = cargo_toml.parse::<toml_edit::DocumentMut>()?;
    if cargo_toml.contains_key("package") {
        implicit_table(&mut cargo_toml, "dependencies")["creusot-contracts"] =
            toml_edit::value(CREUSOT_CONTRACTS_VERSION);
        if !self_version.pre.is_empty() {
            let patch = implicit_table(&mut cargo_toml, "patch");
            implicit_table(patch.as_table_mut().unwrap(), "crates-io")["creusot-contracts"]["path"] =
                toml_edit::value(creusot_contracts_path().display().to_string());
        }
    } else {
        eprintln!(
            "No [package] found in Cargo.toml. Not updating dependencies. If this is a Cargo workspace, you may update the dependencies of a package in <DIR> individually with `cargo creusot new <DIR>`"
        );
    }
    let mut file = std::fs::File::create(cargo_toml_path)?;
    file.write_all(cargo_toml.to_string().as_bytes())?;
    Ok(())
}

/// Get the value for the key if it exists.
/// If the key doesn't exist, insert a `Table` and mark it implicit.
///
/// We don't just use `Index` (`toml[key]`) because it creates an
/// `InlineTable` instead of a `Table`.
/// And we call `set_implcit` because otherwise we would get an empty `[patch]`
/// table next to `[patch.crates-io]` to appear in our generated toml file.
fn implicit_table<'a>(toml: &'a mut toml_edit::Table, key: &'a str) -> &'a mut toml_edit::Item {
    toml.entry(key).or_insert_with(|| {
        let mut table = toml_edit::Table::new();
        table.set_implicit(true);
        table.into()
    })
}
