//! Validate that `ghost!` does not modify program variables

use rustc_hir::HirId;
use rustc_hir_typeck::expr_use_visitor::{Delegate, ExprUseVisitor, PlaceWithHirId};
use rustc_lint::{LateLintPass, LintPass};
use rustc_middle::ty::{Ty, TyCtxt};
use std::collections::HashSet;

use crate::contracts_items::is_ghost_ty;

pub struct GhostValidate {}

impl LintPass for GhostValidate {
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
        if !super::is_ghost_block(cx.tcx, expr.hir_id) {
            return;
        }

        // Check that all captures are ghost/copy
        let mut places = GhostValidatePlaces {
            bound_variables: HashSet::new(),
            tcx: cx.tcx,
            errors: Vec::new(),
        };
        let visitor = ExprUseVisitor::for_clippy(cx, expr.hir_id.owner.def_id, &mut places);
        // Error type is `!`
        let _ = visitor.walk_expr(expr);
        let tcx = cx.tcx;
        for &(id, base, written) in &places.errors {
            let mut err = if written {
                tcx.dcx().struct_err("cannot write to a non-ghost variable in a `ghost!` block")
            } else {
                tcx.dcx().struct_err("cannot move a non-ghost variable into a `ghost!` block")
            };
            err.span(tcx.hir().span(id));
            if let Some(base) = base {
                err.span_note(
                    tcx.hir().span(base),
                    if written {
                        "variable defined here"
                    } else {
                        "variable defined here is not copy"
                    },
                );
            }
            err.emit();
        }
        cx.tcx.dcx().abort_if_errors();
    }
}

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

    /// Determine if the given type `ty` is a `GhostBox`.
    fn is_ghost_box(&self, ty: Ty<'tcx>) -> bool {
        match ty.kind() {
            rustc_type_ir::TyKind::Adt(containing_type, _) => {
                is_ghost_ty(self.tcx, containing_type.did())
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

impl<'tcx> Delegate<'tcx> for GhostValidatePlaces<'tcx> {
    fn consume(&mut self, place_with_id: &PlaceWithHirId<'tcx>, diag_expr_id: HirId) {
        let ty = place_with_id.place.ty();
        // No need to check for copy types, they cannot appear here
        if self.bound_in_block(place_with_id) || self.is_ghost_box(ty) {
            return;
        }
        self.errors.push((diag_expr_id, base_hir_node(place_with_id), false));
    }

    fn borrow(
        &mut self,
        place_with_id: &PlaceWithHirId<'tcx>,
        diag_expr_id: HirId,
        bk: rustc_middle::ty::BorrowKind,
    ) {
        let ty = place_with_id.place.ty();
        if self.bound_in_block(place_with_id) || self.is_ghost_box(ty) {
            return;
        }
        match bk {
            rustc_middle::ty::BorrowKind::Immutable => {}
            rustc_middle::ty::BorrowKind::UniqueImmutable
            | rustc_middle::ty::BorrowKind::Mutable => {
                self.errors.push((diag_expr_id, base_hir_node(place_with_id), true));
            }
        }
    }

    fn mutate(&mut self, assignee_place: &PlaceWithHirId<'tcx>, diag_expr_id: HirId) {
        let ty = assignee_place.place.ty();
        if self.bound_in_block(assignee_place) || self.is_ghost_box(ty) {
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
