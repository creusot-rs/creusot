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
use crate::translation::specification::{self, inv_subst, lower_term_to_why3};
use crate::util;

pub struct GatherInvariants {
    invariants: IndexMap<DefId, (Symbol, Exp)>,
}

impl GatherInvariants {
    pub fn gather<'tcx>(
        ctx: &mut TranslationCtx<'_, 'tcx>,
        names: &mut CloneMap<'tcx>,
        base_id: DefId,
    ) -> GatherInvariants {
        let (thir, expr) = ctx.tcx.thir_body(WithOptConstParam::unknown(base_id.expect_local()));
        let thir = &thir.borrow();

        let mut visitor = InvariantClosures::new(thir);
        use rustc_middle::thir::visit::Visitor;
        visitor.visit_expr(&thir[expr]);
        let invariants: IndexMap<_, (_, _)> = visitor
            .closures
            .into_iter()
            .map(|clos| {
                let term = specification::typing::typecheck(ctx.tcx, clos.expect_local());
                let exp = lower_term_to_why3(ctx, names, clos, term);
                let invariant = specification::get_attr(
                    ctx.tcx.get_attrs(clos),
                    &["creusot", "spec", "invariant"],
                )
                .unwrap();
                let name = util::ts_to_symbol(invariant.args.inner_tokens()).unwrap();

                (clos, (name, exp))
            })
            .collect();

        Self { invariants }
    }

    // Shift the locations of every invariant to be inside their corresponding loop header block
    pub fn with_corrected_locations_and_names<'tcx>(
        mut self,
        tcx: TyCtxt<'tcx>,
        body: &Body<'tcx>,
    ) -> IndexMap<BasicBlock, Vec<(Symbol, Exp)>> {
        let locations = invariant_locations(tcx, body);
        let inv_subst = inv_subst(body);
        locations
            .into_iter()
            .map(|(bb, invs)| {
                let mut inv_exps = Vec::with_capacity(invs.len());

                for inv_id in invs {
                    let mut inv_exp = self.invariants.remove(&inv_id).unwrap();
                    inv_exp.1.subst(&inv_subst);

                    inv_exps.push(inv_exp);
                }
                (bb, inv_exps)
            })
            .collect()
    }
}

// Collect the closures in thir, so that we can do typechecking ourselves, and
// translate the invariant closure from thir.
pub struct InvariantClosures<'a, 'tcx> {
    thir: &'a Thir<'tcx>,
    pub closures: IndexSet<DefId>,
}

impl InvariantClosures<'a, 'tcx> {
    pub fn new(thir: &'a Thir<'tcx>) -> Self {
        InvariantClosures { thir, closures: IndexSet::new() }
    }
}

impl thir::visit::Visitor<'a, 'tcx> for InvariantClosures<'a, 'tcx> {
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

struct InvariantLocations<'tcx> {
    tcx: TyCtxt<'tcx>,
    invariants: IndexMap<BasicBlock, Vec<DefId>>,
}

impl<'tcx> Visitor<'tcx> for InvariantLocations<'tcx> {
    fn visit_rvalue(&mut self, rvalue: &Rvalue<'tcx>, loc: Location) {
        if let Rvalue::Aggregate(box AggregateKind::Closure(id, _), _) = rvalue {
            if util::is_invariant(self.tcx, *id) {
                self.invariants.entry(loc.block).or_insert_with(Vec::new).push(*id);
            }
        }
        self.super_rvalue(rvalue, loc);
    }
}

// Calculate the *actual* location of invariants in MIR
fn invariant_locations(tcx: TyCtxt<'tcx>, body: &Body<'tcx>) -> IndexMap<BasicBlock, Vec<DefId>> {
    let mut results = IndexMap::new();

    let mut invs_gather = InvariantLocations { tcx, invariants: IndexMap::new() };
    invs_gather.visit_body(body);

    for (bb, invs) in invs_gather.invariants.into_iter() {
        let mut target_block = bb;

        loop {
            let mut succs = body.successors(target_block);

            target_block = succs.next().unwrap();

            // Check if `taget_block` is a loop header by testing if it dominates
            // one of its predecessors.
            if let Some(preds) = body.predecessors().get(target_block) {
                let is_loop_header =
                    preds.iter().any(|pred| body.dominators().is_dominated_by(*pred, target_block));

                if is_loop_header {
                    break;
                }
            };

            // If we've hit a switch then stop trying to push the invariants down.
            if body[target_block].terminator().kind.as_switch().is_some() {
                panic!("Could not find loop header")
            }
        }

        results.insert(target_block, invs);
    }

    results
}
