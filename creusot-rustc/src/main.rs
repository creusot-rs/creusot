#![feature(rustc_private)]
extern crate lazy_static;
extern crate rustc_driver;
extern crate rustc_errors;
extern crate rustc_interface;
extern crate rustc_session;

mod options;
use options::CreusotArgsExt as _;

#[macro_use]
extern crate log;

use creusot::callbacks::*;
use creusot_args::CREUSOT_RUSTC_ARGS;
use options::CreusotArgs;
use rustc_driver::RunCompiler;
use rustc_session::{config::ErrorOutputType, EarlyDiagCtxt};
use std::{env, panic, process::Command};

const BUG_REPORT_URL: &'static str = &"https://github.com/creusot-rs/creusot/issues/new";

struct DefaultCallbacks;
impl rustc_driver::Callbacks for DefaultCallbacks {}

fn main() {
    let handler = EarlyDiagCtxt::new(ErrorOutputType::default());

    // Rust verification tools crash too much for the ice hook to report `full` by default
    if std::env::var_os("RUST_BACKTRACE").is_none() {
        std::env::set_var("RUST_BACKTRACE", "0");
    }
    rustc_driver::install_ice_hook(BUG_REPORT_URL, |_| ());

    rustc_driver::init_rustc_env_logger(&handler);
    env_logger::init();

    setup_plugin();
}

fn setup_plugin() {
    let mut args = env::args().collect::<Vec<_>>();

    let is_wrapper = args.get(1).map(|s| s.contains("rustc")).unwrap_or(false);

    if is_wrapper {
        args.remove(1);
    }

    let creusot: Option<CreusotArgs> = if is_wrapper {
        let creusot = match args.iter().find_map(|arg| arg.strip_prefix("--creusot=")) {
            Some(arg) => Some(serde_json::from_str(arg).unwrap()),
            None => None,
        };
        args.retain(|arg| !arg.starts_with("--creusot"));
        creusot
    } else {
        let mut all_args = CreusotArgs::parse_from(&args);
        args = std::mem::take(&mut all_args.rust_flags);
        Some(all_args)
    };

    let sysroot = sysroot_path();
    args.push(format!("--sysroot={}", sysroot));

    let normal_rustc = args.iter().any(|arg| arg.starts_with("--print"));
    let primary_package = std::env::var("CARGO_PRIMARY_PACKAGE").is_ok();
    let has_contracts =
        args.iter().any(|arg| arg == "creusot_contracts" || arg.contains("creusot_contracts="));

    // Did the user ask to compile this crate? Either they explicitly invoked `creusot-rustc` or this is a primary package.
    let user_asked_for = !is_wrapper || primary_package;

    if normal_rustc || !(user_asked_for || has_contracts) {
        RunCompiler::new(&args, &mut DefaultCallbacks).run().unwrap()
    } else {
        match creusot {
            Some(creusot) => {
                for &arg in CREUSOT_RUSTC_ARGS {
                    args.push(arg.to_owned());
                }
                debug!("creusot args={:?}", args);

                let opts = match CreusotArgs::to_options(creusot) {
                    Ok(opts) => opts,
                    Err(msg) => panic!("Error: {msg}"),
                };
                RunCompiler::new(&args, &mut ToWhy::new(opts)).run().unwrap();
            }
            None => RunCompiler::new(&args, &mut DefaultCallbacks).run().unwrap(),
        }
    };
}

fn sysroot_path() -> String {
    let toolchain: toml::Value = toml::from_str(include_str!("../../rust-toolchain")).unwrap();
    let channel = toolchain["toolchain"]["channel"].as_str().unwrap();

    let output = Command::new("rustup")
        .arg("run")
        .arg(channel)
        .arg("rustc")
        .arg("--print")
        .arg("sysroot")
        .output()
        .unwrap();

    String::from_utf8(output.stdout).unwrap().trim().to_owned()
}
