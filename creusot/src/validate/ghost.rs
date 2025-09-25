//! Validate that `ghost!` does not modify program variables

use rustc_hir::{
    Expr, ExprKind, HirId,
    intravisit::{Visitor, walk_expr},
};
use rustc_hir_typeck::expr_use_visitor::{Delegate, ExprUseVisitor, PlaceBase, PlaceWithHirId};
use rustc_lint::{LateContext, LateLintPass, LintPass, LintVec};
use rustc_middle::ty::{BorrowKind, TyCtxt, UpvarId, UpvarPath};
use rustc_span::{Span, Symbol};
use std::collections::HashSet;

use crate::{
    contracts_items::is_pearlite,
    validate::{is_ghost_block, is_ghost_or_snap},
};

pub struct GhostValidate;

impl<'tcx> LintPass for GhostValidate {
    fn name(&self) -> &'static str {
        ""
    }
    fn get_lints(&self) -> LintVec {
        Vec::new()
    }
}

impl<'tcx> LateLintPass<'tcx> for GhostValidate {
    fn check_expr(&mut self, cx: &LateContext<'tcx>, expr: &'tcx Expr<'tcx>) {
        if !is_ghost_block(cx.tcx, expr.hir_id) {
            return;
        }

        let mut control_flow = GhostControlFlow { loop_labels: Vec::new(), errors: Vec::new() };
        control_flow.visit_expr(expr);

        let tcx = cx.tcx;

        // Check that all captures are ghost/copy
        let mut places =
            GhostValidatePlaces { bound_variables: HashSet::new(), tcx, errors: Vec::new() };
        let visitor = ExprUseVisitor::for_clippy(cx, expr.hir_id.owner.def_id, &mut places);
        // Error type is `!`
        let _ = visitor.walk_expr(expr);

        for (span, msg) in control_flow.errors {
            tcx.dcx()
                .struct_span_err(span, msg)
                .with_note("control flow cannot escape the `ghost!` block")
                .emit();
        }
        for &(id, base, written) in &places.errors {
            let mut err = tcx.dcx().struct_span_err(
                tcx.hir_span(id),
                if written {
                    "cannot write to a non-ghost variable in a `ghost!` block"
                } else {
                    "cannot move a non-ghost variable into a `ghost!` block"
                },
            );
            if let Some(base) = base {
                err.span_note(
                    tcx.hir_span(base),
                    if written {
                        "variable defined here"
                    } else {
                        "variable defined here is not copy"
                    },
                );
            }
            err.emit();
        }
    }
}

/// Check that we do not escape the ghost block with e.g. `return`.
struct GhostControlFlow {
    loop_labels: Vec<Option<rustc_ast::Label>>,
    errors: Vec<(Span, &'static str)>,
}

impl<'tcx> Visitor<'tcx> for GhostControlFlow {
    fn visit_expr(&mut self, expr: &'tcx Expr<'tcx>) -> Self::Result {
        match expr.kind {
            ExprKind::Break(dest, _) => {
                if !self.loop_labels.contains(&dest.label) {
                    self.errors.push((expr.span, "cannot `break` to an outer loop in ghost code"))
                }
            }
            ExprKind::Continue(dest) => {
                if !self.loop_labels.contains(&dest.label) {
                    self.errors
                        .push((expr.span, "cannot `continue` to an outer loop in ghost code"))
                }
            }
            ExprKind::Ret { .. } => {
                self.errors.push((expr.span, "cannot use `return` in ghost code"))
            }
            ExprKind::Become { .. } => {
                self.errors.push((expr.span, "cannot use `become` in ghost code"))
            }
            ExprKind::Yield { .. } => {
                self.errors.push((expr.span, "cannot use `yield` in ghost code"))
            }
            ExprKind::Loop(_, label, _, _) => {
                self.loop_labels.push(label);
                walk_expr(self, expr);
                self.loop_labels.pop();
                return;
            }
            _ => {}
        }
        walk_expr(self, expr)
    }
}

/// Check that we do not change program variables in the ghost block.
struct GhostValidatePlaces<'tcx> {
    bound_variables: HashSet<HirId>,
    tcx: TyCtxt<'tcx>,
    /// Contains the hir node of the written node, as well as the (eventual) node for
    /// the definition of the variable.
    ///
    /// The third field determines if the value was written to or moved (for diagnostics)
    errors: Vec<(HirId, Option<HirId>, bool)>,
}

impl<'tcx> GhostValidatePlaces<'tcx> {
    fn bound_in_block(&self, place_with_id: &PlaceWithHirId) -> bool {
        match place_with_id.place.base {
            PlaceBase::Rvalue => true,
            PlaceBase::Local(hir_id) => self.bound_variables.contains(&hir_id),
            PlaceBase::Upvar(upvar_id) => self.bound_variables.contains(&upvar_id.var_path.hir_id),
            _ => false,
        }
    }
}

fn base_hir_node(place: &PlaceWithHirId) -> Option<HirId> {
    match place.place.base {
        PlaceBase::Rvalue | PlaceBase::StaticItem => None,
        PlaceBase::Local(hir_id)
        | PlaceBase::Upvar(UpvarId { var_path: UpvarPath { hir_id }, closure_expr_id: _ }) => {
            Some(hir_id)
        }
    }
}

fn is_ghost_let(tcx: TyCtxt, id: HirId) -> bool {
    for id in tcx.hir_parent_id_iter(id) {
        let attrs = tcx.hir_attrs(id);
        if attrs
            .iter()
            .any(|a| a.path_matches(&[Symbol::intern("creusot"), Symbol::intern("ghost_let")]))
        {
            return true;
        }
    }
    false
}

impl<'tcx> Delegate<'tcx> for GhostValidatePlaces<'tcx> {
    fn consume(&mut self, place_with_id: &PlaceWithHirId<'tcx>, diag_expr_id: HirId) {
        let ty = place_with_id.place.ty();
        let base_id = base_hir_node(place_with_id);
        // No need to check for copy types, they cannot appear here
        if self.bound_in_block(place_with_id)
            || is_ghost_or_snap(self.tcx, ty)
            || base_id.is_some_and(|id| is_ghost_let(self.tcx, id))
        {
            return;
        }

        let mut enclosing_def_ids = self.tcx.hir_parent_iter(place_with_id.hir_id);
        if enclosing_def_ids.any(|(_, node)| {
            node.associated_body()
                .is_some_and(|(def_id, _)| is_pearlite(self.tcx, def_id.to_def_id()))
        }) {
            // Moving into a pearlite closure is ok
            return;
        }
        self.errors.push((diag_expr_id, base_id, false));
    }

    fn use_cloned(&mut self, place_with_id: &PlaceWithHirId<'tcx>, diag_expr_id: HirId) {
        self.consume(place_with_id, diag_expr_id)
    }

    fn borrow(
        &mut self,
        place_with_id: &PlaceWithHirId<'tcx>,
        diag_expr_id: HirId,
        bk: BorrowKind,
    ) {
        let ty = place_with_id.place.ty();
        if self.bound_in_block(place_with_id)
            || is_ghost_or_snap(self.tcx, ty)
            || bk == BorrowKind::Immutable
        {
            return;
        }
        self.errors.push((diag_expr_id, base_hir_node(place_with_id), true));
    }

    fn mutate(&mut self, assignee_place: &PlaceWithHirId<'tcx>, diag_expr_id: HirId) {
        let ty = assignee_place.place.ty();
        if self.bound_in_block(assignee_place) || is_ghost_or_snap(self.tcx, ty) {
            return;
        }
        self.errors.push((diag_expr_id, base_hir_node(assignee_place), true));
    }

    fn fake_read(
        &mut self,
        _: &PlaceWithHirId<'tcx>,
        _: rustc_middle::mir::FakeReadCause,
        _: HirId,
    ) {
        // Fake reads are noops, so no need to do anything
    }

    fn copy(&mut self, _: &PlaceWithHirId<'tcx>, _: HirId) {
        // It is always ok to copy data inside a ghost block
    }

    fn bind(&mut self, binding_place: &PlaceWithHirId<'tcx>, _: HirId) {
        let var = match binding_place.place.base {
            PlaceBase::Local(hir_id) => hir_id,
            _ => unreachable!(),
        };
        self.bound_variables.insert(var);
    }
}
