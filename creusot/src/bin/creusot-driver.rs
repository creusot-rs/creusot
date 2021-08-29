#![feature(rustc_private)]

extern crate rustc_driver;

#[macro_use]
extern crate log;

use creusot::callbacks::*;
use creusot::options::Options;
use rustc_driver::RunCompiler;
use std::env::args as get_args;

fn main() {
    env_logger::init();

    let mut args = get_args().collect::<Vec<_>>();

    let opts = Options::from_args_and_env(&args);

    if !opts.has_contracts || opts.be_rustc {
        rustc_driver::main();
    }

    args.push("-Cpanic=abort".to_owned());
    args.push("-Coverflow-checks=off".to_owned());
    debug!("creusot args={:?}", args);

    let mut callbacks = ToWhy::new(opts);

    RunCompiler::new(&args, &mut callbacks).run().unwrap();
}
