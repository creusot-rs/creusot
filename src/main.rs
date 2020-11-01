#![feature(rustc_private, register_tool)]
#![feature(box_syntax, box_patterns)]
#![register_tool(wprust)]
#![feature(const_panic, or_patterns)]

extern crate rustc_ast;
extern crate rustc_ast_pretty;
extern crate rustc_driver;
extern crate rustc_hir;
extern crate rustc_index;
extern crate rustc_interface;
extern crate rustc_middle;
extern crate rustc_mir;
extern crate rustc_serialize;
extern crate rustc_span;
extern crate rustc_target;
// extern crate serde;
// extern crate polonius;
extern crate polonius_engine;

// #[macro_use] use lazy_static;

use rustc_driver::{Callbacks, Compilation, RunCompiler};
use rustc_hir::{def_id::LOCAL_CRATE, Item};
use rustc_interface::{interface::Compiler, Queries};
use rustc_middle::ty::{TyCtxt, WithOptConstParam};

mod place;
use place::*;

mod translation;
use rustc_mir::dataflow::{impls::MaybeInitializedLocals, Analysis};
use translation::*;
mod analysis;
mod polonius;

#[allow(dead_code)]
mod debug;
mod mlcfg;

struct ToWhy {}

// use polonius_facts::FactLoader;
// use polonius_engine::{Algorithm, Output};

impl Callbacks for ToWhy {
    // Register callback for after MIR borrowck and typechecking is finished
    fn after_analysis<'tcx>(&mut self, _c: &Compiler, queries: &'tcx Queries<'tcx>) -> Compilation {
        queries.global_ctxt().unwrap().peek_mut().enter(translate).unwrap();
        Compilation::Stop
    }
}

use std::env::args as get_args;
fn main() {
    // env_logger::init_from_env(
    // env_logger::Env::default().filter_or(env_logger::DEFAULT_FILTER_ENV, "debug"));
    let mut args = get_args().collect::<Vec<String>>();
    // args.push("-Znll-facts".to_owned());
    args.push("-Cpanic=abort".to_owned());
    args.push("-Coverflow-checks=off".to_owned());
    args.push("-Znll-facts".to_owned());
    // args.push("-Zdump-mir=".to_owned());
    RunCompiler::new(&args, &mut ToWhy {}).run().unwrap();
}

use std::io::Result;

fn is_type_decl(item: &Item) -> bool {
    match item.kind {
        rustc_hir::ItemKind::TyAlias(_, _) => true,
        rustc_hir::ItemKind::OpaqueTy(_) => unimplemented!(),
        rustc_hir::ItemKind::Enum(_, _) => true,
        rustc_hir::ItemKind::Struct(_, _) => true,
        rustc_hir::ItemKind::Union(_, _) => unimplemented!(),
        _ => false,
    }
}

fn translate(tcx: TyCtxt) -> Result<()> {
    let hir_map = tcx.hir();

    // For each module in the current crate collect the type and body declarations
    for (modk, mod_items) in tcx.hir_crate(LOCAL_CRATE).modules.iter() {
        let mut ty_decls = Vec::new();
        let mut mod_bodies = Vec::new();

        for item_id in mod_items.items.iter() {
            if hir_map.maybe_body_owned_by(*item_id).is_some() {
                mod_bodies.push(hir_map.local_def_id(*item_id));
                continue;
            }
            let item = hir_map.item(*item_id);
            if is_type_decl(item) {
                ty_decls.push(hir_map.local_def_id(*item_id));
            }
        }

        let def_path = hir_map.def_path_from_hir_id(*modk).unwrap();

        log::debug!("Translationg module {:?}", def_path);

        if def_path.data.is_empty() {
            // main module
            println!("module Main");
        } else {
            // other modules
            for seg in def_path.data[0..def_path.data.len() - 1].iter() {
                println!("scope {}", seg);
            }

            println!("module {}", def_path.data.last().unwrap());
        }
        println!("{}", mlcfg::PRELUDE);

        for def_id in ty_decls.iter() {
            log::debug!("Translating type declaration {:?}", def_id);
            let adt = tcx.adt_def(*def_id);
            let res = translation::translate_tydecl(tcx, adt);

            println!("{}", res);
        }

        for def_id in mod_bodies.iter() {
            log::debug!("Translating body {:?}", def_id);
            // (Mir-)Borrowck uses `mir_validated`, so we have to force it to
            // execute before we can steal.
            //
            // We want to capture MIR here for the simple reason that it is before
            // Aggregates are destructured. This means that we don't have to deal with the whole
            // 'assign each field and the discriminant' seperately stuff.
            let _ = tcx.mir_borrowck(*def_id);

            // Read Polonius facts.
            let def_path = tcx.def_path(def_id.to_def_id());

            let (body, _) = tcx.mir_promoted(WithOptConstParam::unknown(*def_id));
            let body = body.steal();

            let polonius_info = polonius::PoloniusInfo::new(&body, def_path);

            let def_id = def_id.to_def_id();

            let discr_map = analysis::DiscrTyMap::analyze(&body);

            let res = MaybeInitializedLocals
                .into_engine(tcx, &body)
                .iterate_to_fixpoint()
                .into_results_cursor(&body);
            let translated = FunctionTranslator::new(tcx, &body, polonius_info, res, discr_map)
                .translate(def_id);

            print!("{}", translated);
            // debug::debug(tcx, &body, polonius_info);
            // debug::DebugBody { tcx, pol: polonius_info, move_map, discr_map }.visit_body(&body);
        }

        for _ in 0..def_path.data.len() + 1 {
            println!("end");
        }
    }

    Ok(())
}
