use crate::config::{CREUSOT_STD_VERSION, implicit_table, write};
use anyhow::Result;
use clap::Parser;
use creusot_setup::creusot_paths;
use std::{
    fs,
    io::Write,
    path::{Path, PathBuf},
};

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
    /// Disable standard library
    #[clap(long)]
    pub no_std: bool,
}

fn cargo_template(name: &str, no_std: bool) -> String {
    let creusot_std = if no_std {
        format!("{{ version = \"{CREUSOT_STD_VERSION}\", default-features = false }}")
    } else {
        format!("\"{CREUSOT_STD_VERSION}\"")
    };
    format!(
        r#"[package]
name = "{name}"
version = "0.1.0"
edition = "2024"

[dependencies]
creusot-std = {creusot_std}

[lints.rust]
unexpected_cfgs = {{ level = "warn", check-cfg = ['cfg(creusot)'] }}
"#
    )
}

fn bin_template(name: &str) -> String {
    let name = name.replace("-", "_");
    format!(
        r#"#[allow(unused_imports)]
use creusot_std::prelude::*;
use {name}::*;

fn main() {{
    assert!(add_one(2) == 3);
    println!("Hello, world!");
}}
"#
    )
}

const TEST_TEMPLATE: &str = r#"#[allow(unused_imports)]
use creusot_std::prelude::*;

#[test]
fn it_works() {
    assert_eq!(2 + 2, 4);
}
"#;

const LIB_TEMPLATE: &str = r#"use creusot_std::prelude::*;

#[requires(a@ < i64::MAX@)]
#[ensures(result@ == a@ + 1)]
pub fn add_one(a: i64) -> i64 {
    a + 1
}
"#;

pub fn new(args: NewArgs) -> Result<()> {
    validate_name(&args.name)?;
    if args.args.main && args.args.no_std {
        return Err(anyhow::anyhow!(
            "Cannot create main file in no-std mode, as 'fn main()' depends on 'std'."
        ));
    };
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
    let paths = creusot_paths();
    let cargo_toml = Path::new("Cargo.toml");
    if cargo_toml.exists() {
        patch_dep(cargo_toml)?;
    } else {
        // Rust files are only generated if there wasn't already a Cargo.toml
        write(cargo_toml, &cargo_template(&name, args.no_std));
        if args.tests {
            fs::create_dir_all("tests")?;
            write("tests/test.rs", TEST_TEMPLATE);
        }
        fs::create_dir_all("src")?;
        if args.main {
            write("src/main.rs", &bin_template(&name));
        }
        if args.no_std {
            write("src/lib.rs", format!("#![no_std]\n{LIB_TEMPLATE}").as_str());
        } else {
            write("src/lib.rs", LIB_TEMPLATE);
        }
    }
    let root = if let Some(mut parent) = find_parent_cargo_toml() {
        eprintln!("Info: It seems that you are in a workspace (found {}).", parent.display());
        parent.pop();
        parent
    } else {
        PathBuf::new()
    };
    let why3find_json = paths.why3find_json();
    copy(&why3find_json, root.join("why3find.json"));
    write(root.join(".gitignore"), "target\n_creusot_erasure\n*.coma\n.why3find");
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

/// Do nothing if the target exists.
fn copy(src: impl AsRef<Path>, dst: impl AsRef<Path>) {
    let dst = dst.as_ref();
    if dst.exists() {
        return;
    }
    let src = src.as_ref();
    if let Err(err) = fs::copy(src, dst) {
        panic!("Error copying {} to {}: {err}", src.display(), dst.display());
    }
}

/// Add or update creusot-std in Cargo.toml:
///
/// ```toml
/// [dependencies]
/// creusot-std = "X.Y.Z"
/// ```
fn patch_dep(cargo_toml_path: impl AsRef<Path>) -> Result<()> {
    let cargo_toml_path = cargo_toml_path.as_ref();
    let cargo_toml = std::fs::read_to_string(cargo_toml_path)?;
    let mut cargo_toml = cargo_toml.parse::<toml_edit::DocumentMut>()?;
    if cargo_toml.contains_key("package") {
        implicit_table(cargo_toml.as_table_mut(), "dependencies")["creusot-std"] =
            toml_edit::value(CREUSOT_STD_VERSION);
        // Remove legacy [patch.crates-io]
        // FIXME: remove after 0.12
        if let Some(toml_edit::Item::Table(patch)) = cargo_toml.get_mut("patch")
            && let toml_edit::Item::Table(ref mut crates_io) = patch["crates-io"]
        {
            if let Some(_) = crates_io.remove("creusot-std") {
                eprintln!(
                    "Removed [patch.crates-io.creusot-std] in {} (you should update $HOME/.cargo/config.toml instead with `cargo creusot config --update`)",
                    cargo_toml_path.display()
                );
                if crates_io.is_empty() {
                    patch.remove("crates-io");
                    if patch.is_empty() {
                        cargo_toml.remove("patch");
                    }
                }
            }
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
