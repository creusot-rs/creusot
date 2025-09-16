#![feature(rustc_private)]
extern crate lazy_static;
extern crate rustc_driver;
extern crate rustc_errors;
extern crate rustc_interface;
extern crate rustc_session;

#[macro_use]
extern crate log;

use creusot::callbacks::*;
use creusot_args::{CREUSOT_RUSTC_ARGS, options::CreusotArgs};
use rustc_driver::run_compiler;
use rustc_session::{EarlyDiagCtxt, config::ErrorOutputType};
use std::env;

const BUG_REPORT_URL: &str = "https://github.com/creusot-rs/creusot/issues/new";

struct DefaultCallbacks;
impl rustc_driver::Callbacks for DefaultCallbacks {}

fn main() {
    let handler = EarlyDiagCtxt::new(ErrorOutputType::default());

    // Rust verification tools crash too much for the ice hook to report `full` by default
    if std::env::var_os("RUST_BACKTRACE").is_none() {
        unsafe {
            // Safety: we are in single threaded code
            std::env::set_var("RUST_BACKTRACE", "0");
        }
    }
    rustc_driver::install_ice_hook(BUG_REPORT_URL, |_| ());

    rustc_driver::init_rustc_env_logger(&handler);
    env_logger::init();

    setup_plugin();
}

// Usage: creusot-rustc [RUSTC_OPTIONS] -- [CREUSOT_OPTIONS]
// or     creusot-rustc [RUSTC_OPTIONS] --creusot=JSON_CREUSOT_OPTIONS
fn setup_plugin() {
    let mut args = env::args().collect::<Vec<_>>();

    let creusot = match args.iter().find_map(|arg| arg.strip_prefix("--creusot=")) {
        Some(json) => {
            let creusot = serde_json::from_str(json).unwrap();
            args.retain(|arg| !arg.starts_with("--creusot="));
            Some(creusot)
        }
        None => args.iter().rposition(|arg| arg == "--").map(|pos| {
            let mut creusot_args = args.split_off(pos);
            creusot_args[0] = "creusot-rustc".to_string();
            CreusotArgs::parse_from(creusot_args)
        }),
    };
    let opts = creusot.map(|creusot| {
        creusot.to_options().unwrap_or_else(|msg| {
            eprintln!("Invalid options: {msg}");
            std::process::exit(1)
        })
    });

    let has_contracts =
        args.iter().any(|arg| arg == "creusot_contracts" || arg.contains("creusot_contracts="));

    if has_contracts {
        let Some(opts) = opts else {
            eprintln!("Missing Creusot options");
            std::process::exit(1);
        };
        for &arg in CREUSOT_RUSTC_ARGS {
            args.push(arg.to_owned());
        }
        debug!("creusot args={:?}", args);
        run_compiler(&args, &mut ToWhy::new(opts))
    } else {
        args.push("--cfg=creusot".to_string());
        match opts {
            None => run_compiler(&args, &mut DefaultCallbacks), // This is probably rustc -vV
            Some(opts) => run_compiler(&args, &mut WithoutContracts::new(opts)),
        }
    }
}
