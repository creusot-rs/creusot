#![feature(rustc_private)]
extern crate lazy_static;
extern crate rustc_driver;
extern crate rustc_errors;
extern crate rustc_interface;
extern crate rustc_session;

mod options;
use options::{Args, CreusotArgsExt as _};

#[macro_use]
extern crate log;

use creusot::callbacks::*;
use options::CreusotArgs;
use rustc_driver::{RunCompiler, DEFAULT_LOCALE_RESOURCES};
use rustc_errors::{emitter::EmitterWriter, TerminalUrl};
use rustc_interface::interface::try_print_query_stack;
use rustc_session::{config::ErrorOutputType, EarlyErrorHandler};
use std::{env, panic, panic::PanicInfo, process::Command};

const BUG_REPORT_URL: &'static str = &"https://github.com/xldenis/creusot/issues/new";
const WHY3_VERSION: &'static str = &"1.7.0+git";

lazy_static::lazy_static! {
    static ref ICE_HOOK: Box<dyn Fn(&panic::PanicInfo<'_>) + Sync + Send + 'static> = {
        let hook = panic::take_hook();
        panic::set_hook(Box::new(|info| report_panic(info)));
        hook
    };
}

fn report_panic(info: &PanicInfo) {
    (*ICE_HOOK)(info);

    // Separate the output with an empty line
    eprintln!();
    let fallback_bundle =
        rustc_errors::fallback_fluent_bundle(DEFAULT_LOCALE_RESOURCES.to_vec(), false);

    let emitter = Box::new(EmitterWriter::stderr(
        rustc_errors::ColorConfig::Auto,
        None,
        None,
        fallback_bundle,
        false,
        false,
        None,
        false,
        false,
        TerminalUrl::Auto,
    ));
    let handler = rustc_errors::Handler::with_emitter(true, None, emitter);

    let mut diagnostic = handler.struct_note_without_error("Creusot has panic-ed!");
    diagnostic.note("Oops, that shouldn't have happened, sorry about that.");
    diagnostic.note(format!("Please report this bug over here: {}", BUG_REPORT_URL));

    diagnostic.emit();

    // If backtraces are enabled, also print the query stack
    let backtrace = env::var_os("RUST_BACKTRACE").map_or(false, |x| &x != "0");

    if backtrace {
        try_print_query_stack(&handler, None);
    }
}

struct DefaultCallbacks;
impl rustc_driver::Callbacks for DefaultCallbacks {}

fn main() {
    let handler = EarlyErrorHandler::new(ErrorOutputType::default());
    rustc_driver::init_rustc_env_logger(&handler);
    env_logger::init();
    lazy_static::initialize(&ICE_HOOK);

    setup_plugin();
}

fn setup_plugin() {
    let mut args = env::args().collect::<Vec<_>>();

    let is_wrapper = args.get(1).map(|s| s.contains("rustc")).unwrap_or(false);

    if is_wrapper {
        args.remove(1);
    }

    let creusot: CreusotArgs = if is_wrapper {
        serde_json::from_str(&std::env::var("CREUSOT_ARGS").unwrap()).unwrap()
    } else {
        let all_args = Args::parse_from(&args);
        args = all_args.rust_flags;
        all_args.creusot
    };

    if creusot.check_why3 {
        if let Some(why3_vers) = why3_version() {
            if why3_vers != WHY3_VERSION {
                emit_warning(format!(
                    "the recommended version of why3 is {WHY3_VERSION} (installed: {why3_vers})"
                ));
            }
        } else {
            emit_warning("could not determine installed why3 version".to_string());
        }
    }

    let sysroot = sysroot_path();
    args.push(format!("--sysroot={}", sysroot));

    let normal_rustc = args.iter().any(|arg| arg.starts_with("--print"));
    let primary_package = std::env::var("CARGO_PRIMARY_PACKAGE").is_ok();
    let has_contracts =
        args.iter().any(|arg| arg == "creusot_contracts" || arg.contains("creusot_contracts="));

    // Did the user ask to compile this crate? Either they explicitly invoked `creusot-rustc` or this is a primary package.
    let user_asked_for = !is_wrapper || primary_package;

    if normal_rustc || !(user_asked_for || has_contracts) {
        return RunCompiler::new(&args, &mut DefaultCallbacks {}).run().unwrap();
    } else {
        args.push("-Cpanic=abort".to_owned());
        args.push("-Coverflow-checks=off".to_owned());
        args.push("-Zcrate-attr=feature(register_tool)".to_owned());
        args.push("-Zcrate-attr=register_tool(creusot)".to_owned());
        args.push("-Zcrate-attr=register_tool(why3)".to_owned());
        args.push("-Zcrate-attr=feature(stmt_expr_attributes)".to_owned());
        args.push("-Zcrate-attr=feature(proc_macro_hygiene)".to_owned());
        args.push("-Zcrate-attr=feature(rustc_attrs)".to_owned());
        args.push("-Zcrate-attr=feature(unsized_fn_params)".to_owned());
        args.extend(["--cfg", "creusot"].into_iter().map(str::to_owned));
        debug!("creusot args={:?}", args);

        let opts = CreusotArgs::to_options(creusot);
        let mut callbacks = ToWhy::new(opts);

        RunCompiler::new(&args, &mut callbacks).run().unwrap();
    }
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

fn why3_version() -> Option<String> {
    let output = Command::new("why3").arg("--version").output().ok()?;

    let version = String::from_utf8(output.stdout).ok()?;
    if version.trim().starts_with("Why3 platform, version ") {
        Some(version.trim()[23..].to_owned())
    } else {
        None
    }
}

fn emit_warning(text: String) {
    let fallback_bundle =
        rustc_errors::fallback_fluent_bundle(DEFAULT_LOCALE_RESOURCES.to_vec(), false);

    let emitter = Box::new(EmitterWriter::stderr(
        rustc_errors::ColorConfig::Auto,
        None,
        None,
        fallback_bundle,
        false,
        false,
        None,
        false,
        false,
        TerminalUrl::Auto,
    ));
    let handler = rustc_errors::Handler::with_emitter(true, None, emitter);
    handler.warn(text);
}
