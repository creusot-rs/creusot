//! Validate that `ghost!` does not modify program variables

use rustc_hir::{HirId, intravisit::Visitor as _};
use rustc_hir_typeck::expr_use_visitor::{Delegate, ExprUseVisitor, PlaceWithHirId};
use rustc_lint::{LateLintPass, LintPass};
use rustc_middle::ty::{Ty, TyCtxt};
use rustc_span::{Span, Symbol};
use std::collections::HashSet;

use crate::{
    contracts_items::{get_intrinsic, is_pearlite},
    validate::is_ghost_block,
};

pub struct GhostValidate;

impl<'tcx> LintPass for GhostValidate {
    fn name(&self) -> &'static str {
        ""
    }
    fn get_lints(&self) -> rustc_lint::LintVec {
        Vec::new()
    }
}

impl<'tcx> LateLintPass<'tcx> for GhostValidate {
    fn check_expr(
        &mut self,
        cx: &rustc_lint::LateContext<'tcx>,
        expr: &'tcx rustc_hir::Expr<'tcx>,
    ) {
        if !is_ghost_block(cx.tcx, expr.hir_id) {
            return;
        }

        let mut control_flow = GhostControlFlow { errors: Vec::new() };
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
    errors: Vec<(Span, &'static str)>,
}

impl<'tcx> rustc_hir::intravisit::Visitor<'tcx> for GhostControlFlow {
    fn visit_expr(&mut self, expr: &'tcx rustc_hir::Expr<'tcx>) -> Self::Result {
        match expr.kind {
            rustc_hir::ExprKind::Break { .. } => {
                self.errors.push((expr.span, "cannot use `break` in ghost code"))
            }
            rustc_hir::ExprKind::Continue { .. } => {
                self.errors.push((expr.span, "cannot use `continue` in ghost code"))
            }
            rustc_hir::ExprKind::Ret { .. } => {
                self.errors.push((expr.span, "cannot use `return` in ghost code"))
            }
            rustc_hir::ExprKind::Become { .. } => {
                self.errors.push((expr.span, "cannot use `become` in ghost code"))
            }
            rustc_hir::ExprKind::Yield { .. } => {
                self.errors.push((expr.span, "cannot use `yield` in ghost code"))
            }
            _ => {}
        }
        rustc_hir::intravisit::walk_expr(self, expr)
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
            rustc_hir_typeck::expr_use_visitor::PlaceBase::Rvalue => true,
            rustc_hir_typeck::expr_use_visitor::PlaceBase::Local(hir_id) => {
                self.bound_variables.contains(&hir_id)
            }
            rustc_hir_typeck::expr_use_visitor::PlaceBase::Upvar(upvar_id) => {
                self.bound_variables.contains(&upvar_id.var_path.hir_id)
            }
            _ => false,
        }
    }

    /// Determine if the given type `ty` is a `Ghost`.
    fn is_ghost(&self, ty: Ty<'tcx>) -> bool {
        match ty.kind() {
            rustc_type_ir::TyKind::Adt(containing_type, _) => {
                let intr = get_intrinsic(self.tcx, containing_type.did());
                intr == Some(Symbol::intern("ghost")) || intr == Some(Symbol::intern("snapshot"))
            }
            _ => false,
        }
    }
}

fn base_hir_node(place: &PlaceWithHirId) -> Option<HirId> {
    match place.place.base {
        rustc_hir_typeck::expr_use_visitor::PlaceBase::Rvalue
        | rustc_hir_typeck::expr_use_visitor::PlaceBase::StaticItem => None,
        rustc_hir_typeck::expr_use_visitor::PlaceBase::Local(hir_id)
        | rustc_hir_typeck::expr_use_visitor::PlaceBase::Upvar(rustc_middle::ty::UpvarId {
            var_path: rustc_middle::ty::UpvarPath { hir_id },
            closure_expr_id: _,
        }) => Some(hir_id),
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
            || self.is_ghost(ty)
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
        bk: rustc_middle::ty::BorrowKind,
    ) {
        let ty = place_with_id.place.ty();
        if self.bound_in_block(place_with_id)
            || self.is_ghost(ty)
            || bk == rustc_middle::ty::BorrowKind::Immutable
        {
            return;
        }
        self.errors.push((diag_expr_id, base_hir_node(place_with_id), true));
    }

    fn mutate(&mut self, assignee_place: &PlaceWithHirId<'tcx>, diag_expr_id: HirId) {
        let ty = assignee_place.place.ty();
        if self.bound_in_block(assignee_place) || self.is_ghost(ty) {
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
            rustc_hir_typeck::expr_use_visitor::PlaceBase::Local(hir_id) => hir_id,
            _ => unreachable!(),
        };
        self.bound_variables.insert(var);
    }
}
