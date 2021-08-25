#![feature(rustc_private)]

extern crate rustc_driver;

#[macro_use]
extern crate log;

use creusot::callbacks::*;
use rustc_driver::RunCompiler;
use std::{env::args as get_args, path::Path};
use creusot::options::Options;

fn main() {
    env_logger::init();

    let mut args = get_args().collect::<Vec<_>>();

    // When invoked by cargo `rustc` is prepended to the argument list so remove it
    if args.len() > 1 && Path::new(&args[1]).file_stem() == Some("rustc".as_ref()) {
        args.remove(1);
    }

    let opts = Options::from_args_and_env(&args);

    if !opts.has_contracts || opts.be_rustc {
        rustc_driver::main();
    }

    debug!("creusot args={:?}", args);

    let mut callbacks =
        ToWhy::new(opts);

    RunCompiler::new(&args, &mut callbacks).run().unwrap();
}
