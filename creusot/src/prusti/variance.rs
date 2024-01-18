use super::util::generalize;
use crate::prusti::fn_sig_binder::FnSigBinder;
use rustc_infer::{
    infer::{outlives::env::OutlivesEnvironment, region_constraints::Constraint, TyCtxtInferExt},
    traits::Obligation,
};
use rustc_middle::{
    traits::ObligationCause,
    ty::{
        walk::TypeWalker, Binder, BoundVariableKind, ClauseKind, GenericPredicates, ParamEnv,
        PredicateKind, Region, TyCtxt,
    },
};
use rustc_trait_selection::traits::ObligationCtxt;

/// Returns a set of all regions in a function and an iterator over there constraints
pub(super) fn regions_of_fn<'tcx>(
    tcx: TyCtxt<'tcx>,
    sig: FnSigBinder<'tcx>,
) -> impl Iterator<Item = Region<'tcx>> {
    let eb_regions =
        sig.subst().iter().flat_map(|x| TypeWalker::new(x).filter_map(|x| x.as_region()));
    let lb_regions = sig.sig().bound_vars().iter().filter_map(move |x| match x {
        BoundVariableKind::Region(r) => Some(Region::new_free(tcx, sig.def_id().to_def_id(), r)),
        _ => None,
    });
    eb_regions.chain(lb_regions)
}

/// Returns a set of all regions in a function and an iterator over there constraints
/// RegSubReg constrains relate the regions from the functions definition
/// VarSubReg/RegSubVar constrains indicate additional constraints imposed by subtyping when instantiating the function
pub(super) fn constraints_of_fn<'tcx>(
    tcx: TyCtxt<'tcx>,
    sig: FnSigBinder<'tcx>,
) -> impl Iterator<Item = Constraint<'tcx>> {
    let infcx = tcx.infer_ctxt().build();

    let fn_sig = tcx.liberate_late_bound_regions(sig.def_id().to_def_id(), sig.sig());
    let fn_ty = tcx.mk_fn_ptr(Binder::dummy(fn_sig));

    // Try to call this function in a hypothetical context with the same types but where all the regions are generalized

    // generalize function type and param_env
    let fn_ty_gen = generalize(fn_ty, &infcx);
    let param_env: ParamEnv = generalize(sig.param_env(), &infcx);

    // subtyping constraints
    let ocx = ObligationCtxt::new(&infcx);
    ocx.sub(&ObligationCause::dummy(), param_env, fn_ty, fn_ty_gen).unwrap();

    let mk_obligation =
        |predicate| Obligation::new(tcx, ObligationCause::dummy(), param_env, predicate);

    // predicate constraints
    let predicates: GenericPredicates = tcx.predicates_of(sig.def_id());
    let predicates = predicates.instantiate_identity(tcx).predicates;
    let obligations = predicates.into_iter().map(|x| mk_obligation(x.as_predicate()));
    ocx.register_obligations(obligations);

    // well formedness constraints
    ocx.register_obligation(mk_obligation(
        tcx.mk_predicate(Binder::dummy(PredicateKind::Clause(ClauseKind::WellFormed(
            fn_ty.into(),
        )))),
    ));

    assert!(ocx.select_all_or_error().is_empty());
    let outlives = OutlivesEnvironment::new(param_env);
    infcx.process_registered_region_obligations(&outlives);

    let constraints = infcx.take_and_reset_region_constraints();
    constraints.constraints.into_iter().map(move |(x, _)| x)
}
