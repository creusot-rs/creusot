use indexmap::{IndexMap, IndexSet};

use rustc_data_structures::graph::WithSuccessors;
use rustc_hir::def_id::DefId;
use rustc_middle::mir::{visit::Visitor, AggregateKind, BasicBlock, Body, Location, Rvalue};
use rustc_middle::thir::{self, Expr, ExprKind, Thir};
use rustc_middle::ty::{TyCtxt, WithOptConstParam};
use rustc_span::Symbol;

use why3::mlcfg::Exp;

use crate::clone_map::CloneMap;
use crate::ctx::TranslationCtx;
use crate::translation::specification::{self, inv_subst, lower_pure};
use crate::util;

pub struct GatherSpecClosures {
    invariants: IndexMap<DefId, (Symbol, Exp)>,
    assertions: IndexMap<DefId, Exp>,
}

impl GatherSpecClosures {
    pub fn gather<'tcx>(
        ctx: &mut TranslationCtx<'_, 'tcx>,
        names: &mut CloneMap<'tcx>,
        base_id: DefId,
    ) -> GatherSpecClosures {
        let (thir, expr) =
            ctx.tcx.thir_body(WithOptConstParam::unknown(base_id.expect_local())).unwrap();
        let thir = &thir.borrow();

        let mut visitor = InvariantClosures::new(thir);
        use rustc_middle::thir::visit::Visitor;
        visitor.visit_expr(&thir[expr]);

        let mut assertions: IndexMap<_, _> = Default::default();
        let mut invariants: IndexMap<_, _> = Default::default();
        for clos in visitor.closures.into_iter() {
            if let Some(name) = util::invariant_name(ctx.tcx, clos) {
                let term = specification::typing::typecheck(ctx.tcx, clos.expect_local())
                    .unwrap_or_else(|e| e.emit(ctx.tcx.sess));
                let exp = lower_pure(ctx, names, clos, term);

                invariants.insert(clos, (name, exp));
            } else if util::is_assertion(ctx.tcx, clos) {
                let term = specification::typing::typecheck(ctx.tcx, clos.expect_local())
                    .unwrap_or_else(|e| e.emit(ctx.tcx.sess));
                let exp = lower_pure(ctx, names, clos, term);

                assertions.insert(clos, exp);
            }
        }

        Self { assertions, invariants }
    }

    // Shift the locations of every invariant to be inside their corresponding loop header block
    pub fn with_corrected_locations_and_names<'tcx>(
        mut self,
        tcx: TyCtxt<'tcx>,
        body: &Body<'tcx>,
    ) -> (IndexMap<BasicBlock, Vec<(Symbol, Exp)>>, IndexMap<DefId, Exp>) {
        let locations = invariant_locations(tcx, body);

        let invariants = locations
            .into_iter()
            .map(|(loc, invs)| {
                let inv_subst = inv_subst(tcx, body, loc.start_location());
                let inv_exps: Vec<_> = invs
                    .into_iter()
                    .map(|id| {
                        let mut inv = self.invariants.remove(&id).unwrap();
                        inv.1.subst(&inv_subst);
                        inv
                    })
                    .collect();

                (loc, inv_exps)
            })
            .collect();

        let mut ass_loc = AssertionLocations { tcx, locations: IndexMap::new() };
        ass_loc.visit_body(body);
        let locations = ass_loc.locations;

        let assertions = self
            .assertions
            .into_iter()
            .map(|mut ass| {
                let inv_subst = inv_subst(tcx, body, locations[&ass.0]);

                ass.1.subst(&inv_subst);
                ass
            })
            .collect();
        assert!(self.invariants.is_empty());
        (invariants, assertions)
    }
}

// Collect the closures in thir, so that we can do typechecking ourselves, and
// translate the invariant closure from thir.
pub struct InvariantClosures<'a, 'tcx> {
    thir: &'a Thir<'tcx>,
    pub closures: IndexSet<DefId>,
}

impl<'a, 'tcx> InvariantClosures<'a, 'tcx> {
    pub fn new(thir: &'a Thir<'tcx>) -> Self {
        InvariantClosures { thir, closures: IndexSet::new() }
    }
}

impl<'a, 'tcx> thir::visit::Visitor<'a, 'tcx> for InvariantClosures<'a, 'tcx> {
    fn thir(&self) -> &'a Thir<'tcx> {
        self.thir
    }

    fn visit_expr(&mut self, expr: &Expr<'tcx>) {
        if let ExprKind::Closure { closure_id, .. } = expr.kind {
            self.closures.insert(closure_id);
        }
        thir::visit::walk_expr(self, expr);
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
