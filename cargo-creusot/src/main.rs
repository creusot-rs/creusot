use clap::*;
use creusot_args::options::Args;
use std::{
    env,
    process::{exit, Command},
};

fn main() {
    let args = Args::parse_from(std::env::args().skip(1));

    let creusot_rustc_path = std::env::current_exe()
        .expect("current executable path invalid")
        .with_file_name("creusot-rustc");

    let cargo_path = env::var("CARGO_PATH").unwrap_or_else(|_| "cargo".to_string());
    let cargo_cmd = if std::env::var_os("CREUSOT_CONTINUE").is_some() { "build" } else { "check" };
    let toolchain = toolchain_channel()
        .expect("Expected `cargo-creusot` to be built with a valid toolchain file");
    let mut cmd = Command::new(cargo_path);
    cmd.arg(format!("+{toolchain}"))
        .arg(&cargo_cmd)
        .args(args.rust_flags)
        .env("RUSTC_WRAPPER", creusot_rustc_path)
        .env("CARGO_CREUSOT", "1");

    cmd.env("CREUSOT_ARGS", serde_json::to_string(&args.creusot).unwrap());

    let exit_status = cmd.status().expect("could not run cargo");
    if !exit_status.success() {
        exit(exit_status.code().unwrap_or(-1));
    }
}

fn toolchain_channel() -> Option<String> {
    let toolchain: toml::Value = toml::from_str(include_str!("../../rust-toolchain")).ok()?;
    let channel = toolchain["toolchain"]["channel"].as_str()?;
    Some(channel.into())
}
