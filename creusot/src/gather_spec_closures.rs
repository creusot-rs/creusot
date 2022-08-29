use indexmap::{IndexMap, IndexSet};

use crate::{
    ctx::TranslationCtx,
    translation::specification::{inv_subst, typing::Term},
    util::{self, is_ghost_closure},
};
use creusot_rustc::{
    data_structures::graph::WithSuccessors,
    hir::def_id::DefId,
    middle::{
        mir::visit::Visitor,
        ty::{TyCtxt, TyKind},
    },
    smir::mir::{AggregateKind, BasicBlock, Body, Location, Operand, Rvalue},
    span::Symbol,
};

pub fn corrected_invariant_names_and_locations<'tcx>(
    ctx: &mut TranslationCtx<'_, 'tcx>,
    def_id: DefId,
    body: &Body<'tcx>,
) -> (IndexMap<BasicBlock, Vec<(Symbol, Term<'tcx>)>>, IndexMap<DefId, Term<'tcx>>) {
    let mut visitor = InvariantClosures::new(ctx.tcx, def_id);
    visitor.visit_body(&body);

    let mut assertions: IndexMap<_, _> = Default::default();
    // let mut ghosts: IndexMap<_, _> = Default::default();
    let mut invariants: IndexMap<_, _> = Default::default();

    for clos in visitor.closures.into_iter() {
        if let Some(name) = util::invariant_name(ctx.tcx, clos) {
            let term = ctx.term(clos).unwrap().clone();

            invariants.insert(clos, (name, term));
        } else if util::is_assertion(ctx.tcx, clos) {
            let term = ctx.term(clos).unwrap().clone();

            assertions.insert(clos, term);
        } else if util::is_ghost(ctx.tcx, clos) {
            let term = ctx.term(clos).unwrap().clone();

            // A hack should probably be separately tracked
            assertions.insert(clos, term);
        }
    }

    let locations = invariant_locations(ctx.tcx, body);

    let correct_inv = locations
        .into_iter()
        .map(|(loc, invs)| {
            let inv_exps: Vec<_> = invs
                .into_iter()
                .map(|id| {
                    let mut inv = invariants.remove(&id.1).unwrap();
                    let inv_subst = inv_subst(body, id.0);
                    inv.1.subst(&inv_subst);
                    inv
                })
                .collect();

            (loc, inv_exps)
        })
        .collect();

    let mut ass_loc = ClosureLocations { locations: IndexMap::new() };
    ass_loc.visit_body(body);
    let locations = ass_loc.locations;

    let assertions = assertions
        .into_iter()
        .map(|mut ass| {
            let inv_subst = inv_subst(body, locations[&ass.0]);

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
    pub def_id: DefId,
    pub closures: IndexSet<DefId>,
}

impl<'tcx> InvariantClosures<'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>, def_id: DefId) -> Self {
        InvariantClosures { tcx, def_id, closures: IndexSet::new() }
    }
}

impl<'tcx> Visitor<'tcx> for InvariantClosures<'tcx> {
    fn visit_rvalue(&mut self, rvalue: &Rvalue<'tcx>, loc: Location) {
        match rvalue {
            Rvalue::Aggregate(box AggregateKind::Closure(id, _), _) => {
                self.closures.insert(*id);
            }
            Rvalue::Use(Operand::Constant(box ck)) => {
                if let Some(c) = ck.literal.const_for_ty() {
                    if let Some(def_id) = is_ghost_closure(self.tcx, c.ty()) {
                        self.closures.insert(def_id);
                    }
                }
            }
            _ => {}
        }
        self.super_rvalue(rvalue, loc);
    }
}

struct ClosureLocations {
    locations: IndexMap<DefId, Location>,
}

impl<'tcx> Visitor<'tcx> for ClosureLocations {
    fn visit_rvalue(&mut self, rvalue: &Rvalue<'tcx>, loc: Location) {
        match rvalue {
            Rvalue::Aggregate(box AggregateKind::Closure(id, _), _) => {
                self.locations.insert(*id, loc);
            }
            Rvalue::Use(Operand::Constant(box ck)) => {
                if let Some(c) = ck.literal.const_for_ty() {
                    if let TyKind::Closure(def_id, _) = c.ty().peel_refs().kind() {
                        self.locations.insert(*def_id, loc);
                    }
                }
            }
            _ => {}
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
) -> IndexMap<BasicBlock, Vec<(Location, DefId)>> {
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

        results.entry(target).or_insert_with(Vec::new).push((loc, clos));
    }

    results
}
