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
use rustc_interface::{interface::Compiler, Queries};
use rustc_middle::{mir::{Body, Location, MirPhase, Place, visit::PlaceContext, Statement}, ty::{InstanceDef, TyCtxt, WithOptConstParam}};
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

use std::{env::args as get_args};
fn main() {
    let mut args = get_args().collect::<Vec<String>>();
    // args.push("-Znll-facts".to_owned());
    args.push("-Cpanic=abort".to_owned());
    args.push("-Coverflow-checks=off".to_owned());
    run_compiler(&args, &mut ToWhy {}, None, None, None).unwrap();
}

use std::io::Result;

fn translate(tcx: TyCtxt) -> Result<()> {
    for def_id in tcx.body_owners() {
        // (Mir-)Borrowck uses `mir_validated`, so we have to force it to
        // execute before we can steal.
        //
        // We want to capture MIR here for the simple reason that it is before
        // Aggregates are destructured. This means that we don't have to deal with the whole
        // 'assign each field and the discriminant' seperately stuff.
        let _ = tcx.mir_borrowck(def_id);

        let (body, _) = tcx.mir_promoted(WithOptConstParam::unknown(def_id));
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
        dbg!(def_id);
        (S { tcx, body: &body }).visit_body(&body);
    }
    Ok(())
}

struct S<'a, 'tcx> {
    tcx: TyCtxt<'tcx>,
    body: &'a Body<'tcx>,
}

use rustc_middle::mir::visit::Visitor;
use rustc_middle::mir::{BorrowKind::*, Rvalue::*, StatementKind::*};
use crate::whycfg::MlCfgExp::{BorrowMut, Final};

impl<'a, 'tcx> Visitor<'tcx> for S<'a, 'tcx> {
    fn visit_place(&mut self, place: &Place<'tcx>, _: PlaceContext, _: Location) {
        let mp = from_place(self.tcx, self.body, place);
        // dbg!(&mp);
        // println!("{}", rhs_to_why_exp(&mp));
    }

    fn visit_statement(&mut self, statement: &Statement< 'tcx>, _:Location) {
        match &statement.kind {
            Assign(box (l, op)) => {
                println!("[[[{:?}]]]", statement);
                let lhs = from_place(self.tcx, self.body, l);
                match op {
                    Use(u) => {
                        if u.place().is_none() { return; }

                        let rhs = rhs_to_why_exp(&from_place(self.tcx, self.body, &u.place().unwrap()));
                        println!("{}", create_assign(self.tcx, &lhs, rhs));
                    }
                    Ref(_, bk, pl) => {
                        if let Mut { .. } = bk {
                            let rhs = from_place(self.tcx, self.body, pl);

                            let s1 = create_assign(self.tcx, &lhs, BorrowMut(box rhs_to_why_exp(&rhs)));
                            let s2 = create_assign(self.tcx, &rhs, Final(box rhs_to_why_exp(&lhs)));

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
