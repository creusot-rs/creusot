use crate::contracts_items::{is_check_ghost, is_check_terminates, is_law, is_logic};
use rustc_hir::def_id::DefId;
use rustc_middle::ty::TyCtxt;

type AttributeFn = fn(TyCtxt, DefId) -> bool;

const INCOMPATIBLE_ATTRIBUTES: &[(AttributeFn, AttributeFn, &str)] = &[
    (is_logic, is_check_ghost, "logical function cannot use the `check(ghost)` attribute"),
    (
        is_logic,
        is_check_terminates,
        "logical function cannot use the `check(terminates)` attribute",
    ),
];

pub(super) fn validate_incorrect_attributes(tcx: TyCtxt, def_id: DefId) {
    if is_law(tcx, def_id)
        && !(tcx.trait_of_assoc(def_id).is_some() || tcx.trait_impl_of_assoc(def_id).is_some())
    {
        tcx.dcx().span_err(
            tcx.def_span(def_id),
            "Laws can only be declared in trait definitions or implementations",
        );
    }
    for &(attr1, attr2, reason) in INCOMPATIBLE_ATTRIBUTES {
        if attr1(tcx, def_id) && attr2(tcx, def_id) {
            tcx.dcx().span_err(tcx.def_span(def_id), reason);
        }
    }
}
