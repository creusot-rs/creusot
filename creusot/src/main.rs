#![feature(rustc_private, register_tool)]
#![feature(box_syntax, box_patterns, control_flow_enum)]
#![feature(in_band_lifetimes)]
#![register_tool(creusot)]
#![feature(const_panic)]

extern crate rustc_ast;
extern crate rustc_data_structures;
extern crate rustc_driver;
extern crate rustc_errors;
extern crate rustc_hir;
extern crate rustc_index;
extern crate rustc_interface;
extern crate rustc_middle;
extern crate rustc_mir;
extern crate rustc_mir_build;
extern crate rustc_resolve;
extern crate rustc_session;
extern crate rustc_span;
extern crate rustc_target;
extern crate rustc_trait_selection;
extern crate smallvec;

#[macro_use]
extern crate log;

mod analysis;
mod closure_gatherer;
pub mod ctx;
mod extended_location;
mod resolve;
mod translation;
pub mod util;

#[allow(dead_code)]
mod debug;

mod modules;

#[allow(dead_code)]
mod rustc_extensions;

mod cleanup_spec_closures;


use rustc_driver::{abort_on_err, Callbacks, Compilation, RunCompiler};
use rustc_interface::{interface::Compiler, Config, Queries};

use std::env::args as get_args;

use cleanup_spec_closures::*;

use translation::*;
use util::sysroot_path;

struct ToWhy {
    output_file: Option<String>,
}

impl Callbacks for ToWhy {
    fn config(&mut self, config: &mut Config) {
        config.override_queries = Some(|_sess, providers, _external_providers| {
            providers.mir_built = |tcx, def_id| {
                let mir = (rustc_interface::DEFAULT_QUERY_PROVIDERS.mir_built)(tcx, def_id);
                let mut mir = mir.steal();
                cleanup_spec_closures(tcx, def_id.def_id_for_type_of(), &mut mir);
                tcx.alloc_steal_mir(mir)
            };
        })
    }

    fn after_expansion<'tcx>(&mut self, c: &Compiler, queries: &'tcx Queries<'tcx>) -> Compilation {
        let session = c.session();
        let resolver = {
            let (_, resolver, _) = &*abort_on_err(queries.expansion(), session).peek();
            resolver.clone()
        };

        queries.prepare_outputs().unwrap();

        queries.global_ctxt().unwrap();

        queries
            .global_ctxt()
            .unwrap()
            .peek_mut()
            .enter(|tcx| {
                let session = c.session();
                // TODO: Resolve extern crates
                crate::translation::translate(&self.output_file, session, tcx, resolver)
            })
            .unwrap();
        Compilation::Stop
    }
}

fn main() {
    env_logger::init();

    let mut args = get_args().collect::<Vec<String>>();

    let output_file = args.iter().position(|a| a == "-o").map(|ix| args[ix + 1].clone());

    args.push(format!("--sysroot={}", sysroot_path()));
    args.push("-Cpanic=abort".to_owned());
    args.push("-Coverflow-checks=off".to_owned());
    // args.push("-Znll-facts".to_owned());
    RunCompiler::new(&args, &mut ToWhy { output_file }).run().unwrap();
}

