use indexmap::{IndexMap, IndexSet};

use rustc_data_structures::graph::WithSuccessors;
use rustc_hir::def_id::DefId;
use rustc_middle::mir::{visit::Visitor, AggregateKind, BasicBlock, Body, Location, Rvalue};
use rustc_middle::ty::TyCtxt;
use tool_lib::Symbol;

use why3::exp::Exp;

use crate::clone_map::CloneMap;
use crate::ctx::TranslationCtx;
use crate::translation::specification::{inv_subst, lower_pure};
use crate::util;

pub fn corrected_invariant_names_and_locations<'tcx>(
    ctx: &mut TranslationCtx<'_, 'tcx>,
    names: &mut CloneMap<'tcx>,
    body: &Body<'tcx>,
) -> (IndexMap<BasicBlock, Vec<(Symbol, Exp)>>, IndexMap<DefId, Exp>) {
    let mut visitor = InvariantClosures::new(ctx.tcx);
    visitor.visit_body(&body);

    let mut assertions: IndexMap<_, _> = Default::default();
    let mut invariants: IndexMap<_, _> = Default::default();
    for clos in visitor.closures.into_iter() {
        if let Some(name) = util::invariant_name(ctx.tcx, clos) {
            let term = ctx.term(clos).unwrap().clone();
            let exp = lower_pure(ctx, names, clos, term);

            invariants.insert(clos, (name, exp));
        } else if util::is_assertion(ctx.tcx, clos) {
            let term = ctx.term(clos).unwrap().clone();
            let exp = lower_pure(ctx, names, clos, term);

            assertions.insert(clos, exp);
        }
    }

    let locations = invariant_locations(ctx.tcx, body);

    let correct_inv = locations
        .into_iter()
        .map(|(loc, invs)| {
            let inv_subst = inv_subst(ctx.tcx, body, loc.start_location());
            let inv_exps: Vec<_> = invs
                .into_iter()
                .map(|id| {
                    let mut inv = invariants.remove(&id).unwrap();
                    inv.1.subst(&inv_subst);
                    inv
                })
                .collect();

            (loc, inv_exps)
        })
        .collect();

    let mut ass_loc = AssertionLocations { tcx: ctx.tcx, locations: IndexMap::new() };
    ass_loc.visit_body(body);
    let locations = ass_loc.locations;

    let assertions = assertions
        .into_iter()
        .map(|mut ass| {
            let inv_subst = inv_subst(ctx.tcx, body, locations[&ass.0]);

            ass.1.subst(&inv_subst);
            ass
        })
        .collect();
    assert!(invariants.is_empty());
    (correct_inv, assertions)
}

// Collect the closures in thir, so that we can do typechecking ourselves, and
// translate the invariant closure from thir.
pub struct InvariantClosures<'tcx> {
    pub tcx: TyCtxt<'tcx>,
    pub closures: IndexSet<DefId>,
}

impl<'tcx> InvariantClosures<'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>) -> Self {
        InvariantClosures { tcx, closures: IndexSet::new() }
    }
}

impl<'tcx> Visitor<'tcx> for InvariantClosures<'tcx> {
    fn visit_rvalue(&mut self, rvalue: &Rvalue<'tcx>, loc: Location) {
        if let Rvalue::Aggregate(box AggregateKind::Closure(id, _), _) = rvalue {
            self.closures.insert(*id);
        }
        self.super_rvalue(rvalue, loc);
    }
}

struct AssertionLocations<'tcx> {
    tcx: TyCtxt<'tcx>,
    locations: IndexMap<DefId, Location>,
}

impl<'tcx> Visitor<'tcx> for AssertionLocations<'tcx> {
    fn visit_rvalue(&mut self, rvalue: &Rvalue<'tcx>, loc: Location) {
        if let Rvalue::Aggregate(box AggregateKind::Closure(id, _), _) = rvalue {
            if util::is_assertion(self.tcx, *id) {
                self.locations.insert(*id, loc);
            }
        }
        self.super_rvalue(rvalue, loc);
    }
}

struct InvariantLocations<'tcx> {
    tcx: TyCtxt<'tcx>,
    invariants: IndexMap<Location, DefId>,
}

impl<'tcx> Visitor<'tcx> for InvariantLocations<'tcx> {
    fn visit_rvalue(&mut self, rvalue: &Rvalue<'tcx>, loc: Location) {
        if let Rvalue::Aggregate(box AggregateKind::Closure(id, _), _) = rvalue {
            if util::is_invariant(self.tcx, *id) {
                self.invariants.insert(loc, *id);
            }
        }
        self.super_rvalue(rvalue, loc);
    }
}

// Calculate the *actual* location of invariants in MIR
fn invariant_locations<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
) -> IndexMap<BasicBlock, Vec<DefId>> {
    let mut results = IndexMap::new();

    let mut invs_gather = InvariantLocations { tcx, invariants: IndexMap::new() };
    invs_gather.visit_body(body);

    for (loc, clos) in invs_gather.invariants.into_iter() {
        let mut target: BasicBlock = loc.block;

        loop {
            let mut succs = body.successors(target);

            target = succs.next().unwrap();

            // Check if `taget_block` is a loop header by testing if it dominates
            // one of its predecessors.
            if let Some(preds) = body.predecessors().get(target) {
                let is_loop_header =
                    preds.iter().any(|pred| body.dominators().is_dominated_by(*pred, target));

                if is_loop_header {
                    break;
                }
            };

            // If we've hit a switch then stop trying to push the invariants down.
            if body[target].terminator().kind.as_switch().is_some() {
                panic!("Could not find loop header")
            }
        }

        results.entry(target).or_insert_with(Vec::new).push(clos);
    }

    results
}
