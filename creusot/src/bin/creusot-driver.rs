#![feature(rustc_private, box_syntax)]

extern crate lazy_static;
extern crate rustc_driver;
extern crate rustc_errors;
extern crate rustc_interface;

#[macro_use]
extern crate log;

use creusot::callbacks::*;
use creusot::options::Options;
use rustc_driver::RunCompiler;
use rustc_interface::interface::try_print_query_stack;
use std::env::args as get_args;
use std::panic::PanicInfo;
use std::{env, panic};

const BUG_REPORT_URL: &'static str = &"https://github.com/xldenis/creusot/issues/new";

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

    let emitter = box rustc_errors::emitter::EmitterWriter::stderr(
        rustc_errors::ColorConfig::Auto,
        None,
        false,
        false,
        None,
        false,
    );
    let handler = rustc_errors::Handler::with_emitter(true, None, emitter);

    let mut diagnostic = handler.struct_note_without_error("Creusot has panic-ed!");
    diagnostic.note("Oops, that shouldn't have happened, sorry about that.");
    diagnostic.note(&format!("Please report this bug over here: {}", BUG_REPORT_URL));

    diagnostic.emit();

    // If backtraces are enabled, also print the query stack
    let backtrace = env::var_os("RUST_BACKTRACE").map_or(false, |x| &x != "0");

    if backtrace {
        try_print_query_stack(&handler, None);
    }
}

fn main() {
    env_logger::init();

    let mut args = get_args().collect::<Vec<_>>();

    let opts = Options::from_args_and_env(&args);

    if !opts.has_contracts || opts.be_rustc {
        rustc_driver::main();
    }

    lazy_static::initialize(&ICE_HOOK);

    args.push("-Cpanic=abort".to_owned());
    args.push("-Coverflow-checks=off".to_owned());
    debug!("creusot args={:?}", args);

    let mut callbacks = ToWhy::new(opts);

    RunCompiler::new(&args, &mut callbacks).run().unwrap();
}
