#![feature(rustc_private, register_tool)]
#![feature(box_syntax, box_patterns)]
#![register_tool(wprust)]

extern crate rustc_ast;
extern crate rustc_ast_pretty;
extern crate rustc_driver;
extern crate rustc_hir;
extern crate rustc_index;
extern crate rustc_interface;
extern crate rustc_middle;
extern crate rustc_mir;
extern crate rustc_span;
extern crate rustc_target;

use rustc_driver::{run_compiler, Callbacks, Compilation};
use rustc_hir::{def_id::LOCAL_CRATE, Item};
use rustc_interface::{interface::Compiler, Queries};
use rustc_middle::{
    mir::{
        visit::{PlaceContext, TyContext},
        Body, Location, MirPhase, Place, Statement,
    },
    ty::{InstanceDef, Ty, TyCtxt, WithOptConstParam},
};
use rustc_mir::transform::run_passes;

mod place;
use place::*;

mod translation;
use translation::*;
mod whycfg;

struct ToWhy {}

// use polonius_facts::FactLoader;
// use polonius_engine::{Algorithm, Output};

impl Callbacks for ToWhy {
    // Register callback for after MIR borrowck and typechecking is finished
    fn after_analysis<'tcx>(&mut self, _c: &Compiler, queries: &'tcx Queries<'tcx>) -> Compilation {
        queries.global_ctxt().unwrap().peek_mut().enter(|tcx| translate(tcx)).unwrap();
        Compilation::Stop
    }
}

use std::env::args as get_args;
fn main() {
    env_logger::init_from_env(
        env_logger::Env::default().filter_or(env_logger::DEFAULT_FILTER_ENV, "debug"));
    let mut args = get_args().collect::<Vec<String>>();
    // args.push("-Znll-facts".to_owned());
    args.push("-Cpanic=abort".to_owned());
    args.push("-Coverflow-checks=off".to_owned());
    run_compiler(&args, &mut ToWhy {}, None, None, None).unwrap();
}

use std::io::Result;

fn is_type_decl<'tcx>(item: &Item<'tcx>) -> bool {
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

        log::debug!("Translationg module {:?}", modk);

        for def_id in ty_decls.iter() {
            log::debug!("Translating type declaration {:?}", def_id);
            let adt = tcx.adt_def(*def_id);
            let res = TranslationCtx { tcx: tcx}.translate_tydecl(adt);

            log::debug!("Result {:?}", res);
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

            let (body, _) = tcx.mir_promoted(WithOptConstParam::unknown(*def_id));
            let mut body = body.steal();
            let def_id = def_id.to_def_id();

            run_passes(
                tcx,
                &mut body,
                InstanceDef::Item(WithOptConstParam::unknown(def_id)),
                None,
                MirPhase::Build,
                &[],
            );
            (S { tcx, body: &body }).visit_body(&body);
        }
    }

    // Option 1:
    // 1. Get modules being translated from crate
    // 2. Translate all modules
    // 3. Dump modules

    // Option 2:
    // 1. Traverse from main function
    // 2. When a new DefId is encountered, translate it
    // 3. Accumulate results in a Map for each module
    // 4. Dump resulting modules

    // Advantage of first approach: Clear control flow of compilation
    // Advantage of second approach: More minimal translated result
    // Disadvantage of first approach: Must translate all of a module
    // Disadvantage of second approach: More complex control flow and
    // accumlating map makes things more complex

    Ok(())
}

struct S<'a, 'tcx> {
    tcx: TyCtxt<'tcx>,
    body: &'a Body<'tcx>,
}

use crate::whycfg::MlCfgExp::{BorrowMut, Final};
use rustc_middle::mir::visit::Visitor;
use rustc_middle::mir::{BorrowKind::*, Rvalue::*, StatementKind::*};

impl<'a, 'tcx> Visitor<'tcx> for S<'a, 'tcx> {
    fn visit_place(&mut self, place: &Place<'tcx>, _: PlaceContext, _: Location) {
        // let mp = from_place(self.tcx, self.body, place);
        // dbg!(&mp);
        // println!("{}", rhs_to_why_exp(&mp));
    }

    fn visit_ty(&mut self, ty: Ty<'tcx>, _: TyContext) {
        let t = TranslationCtx { tcx: self.tcx }.translate_ty(ty);

        dbg!(t);
    }

    fn visit_statement(&mut self, statement: &Statement<'tcx>, _: Location) {
        match &statement.kind {
            Assign(box (l, op)) => {
                println!("[[[{:?}]]]", statement);
                let lhs = from_place(self.tcx, self.body, l);
                match op {
                    Use(u) => {
                        if u.place().is_none() {
                            return;
                        }

                        let rhs =
                            rhs_to_why_exp(&from_place(self.tcx, self.body, &u.place().unwrap()));
                        println!("{}", create_assign(&lhs, rhs));
                    }
                    Ref(_, bk, pl) => {
                        if let Mut { .. } = bk {
                            let rhs = from_place(self.tcx, self.body, pl);

                            let s1 = create_assign(&lhs, BorrowMut(box rhs_to_why_exp(&rhs)));
                            let s2 = create_assign(&rhs, Final(box rhs_to_why_exp(&lhs)));

                            println!("{}", s1);
                            println!("{}", s2);
                        }
                    }
                    _ => {}
                }
            }
            _ => {}
        }
    }
}
