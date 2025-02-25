use anyhow::Result;
use clap::Parser;
use std::{
    fs,
    io::Write,
    process::{Command, Stdio},
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
    /// Path to local creusot-contracts relative to the generated Cargo.toml
    #[clap(long)]
    pub creusot_contracts: Option<String>,
}

fn cargo_template(name: &str, dep: &str) -> String {
    format!(
        r#"[package]
name = "{name}"
version = "0.1.0"
edition = "2024"

[dependencies]
creusot-contracts = {dep}

[lints.rust]
unexpected_cfgs = {{ level = "warn", check-cfg = ['cfg(creusot)'] }}
"#
    )
}

fn bin_template(name: &str) -> String {
    let name = name.replace("-", "_");
    format!(
        r#"#![cfg_attr(
    not(creusot),
    feature(stmt_expr_attributes, proc_macro_hygiene, register_tool)
)]
#![cfg_attr(not(creusot), register_tool(creusot))]

#[allow(unused_imports)]
use creusot_contracts::*;
use {name}::*;

#[allow(creusot::experimental)]
fn main() {{
    assert!(add_one(2) == 3);
    println!("Hello, world!");
}}
"#
    )
}

const TEST_TEMPLATE: &str = r#"#![cfg_attr(not(creusot), feature(stmt_expr_attributes, proc_macro_hygiene))]
use creusot_contracts::*;

#[test]
fn it_works() {
    assert_eq!(2 + 2, 4);
}
"#;

const LIB_TEMPLATE: &str = r#"#![cfg_attr(not(creusot), feature(stmt_expr_attributes, proc_macro_hygiene))]
use creusot_contracts::*;

#[requires(a@ < i64::MAX@)]
#[ensures(result@ == a@ + 1)]
pub fn add_one(a: i64) -> i64 {
    a + 1
}
"#;

const RUST_TOOLCHAIN: &str = r#"[toolchain]
channel = "nightly-2024-07-25"
components = [ "rustfmt" ]
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
    let contract_dep = match args.creusot_contracts {
        Some(path) => format!(r#"{{ path = "{}" }}"#, path),
        None => r#""*""#.to_string(),
    };
    write("Cargo.toml", &cargo_template(&name, &contract_dep));
    write("rust-toolchain", RUST_TOOLCHAIN);
    if args.tests {
        fs::create_dir_all("tests")?;
        write("tests/test.rs", TEST_TEMPLATE);
    }
    fs::create_dir_all("src")?;
    if args.main {
        write("src/main.rs", &bin_template(&name));
    }
    write("src/lib.rs", LIB_TEMPLATE);
    Command::new("cargo").args(["creusot", "config"]).stdout(Stdio::null()).status()?;
    Ok(())
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
/// Warn if writing fails, then keep going
fn write(path: &str, contents: &str) {
    fs::File::create_new(path)
        .and_then(|mut file| file.write_all(contents.as_ref()))
        .unwrap_or_else(|e| {
            if e.kind() == std::io::ErrorKind::AlreadyExists {
                eprintln!("File '{}' already exists. (Skipped)", path);
            } else {
                eprintln!("Could not write to '{}': {} (Skipped)", path, e);
            }
        });
}
