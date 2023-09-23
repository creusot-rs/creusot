use super::util::generalize;
use rustc_infer::{
    infer::{
        outlives::env::OutlivesEnvironment, region_constraints::Constraint, InferCtxt,
        RegionVariableOrigin, TyCtxtInferExt,
    },
    traits::Obligation,
};
use rustc_middle::{
    traits::ObligationCause,
    ty::{
        Binder, BoundVariableKind, ClauseKind, EarlyBinder, FnSig, GenericPredicates,
        InternalSubsts, ParamEnv, PredicateKind, Region, SubstsRef, Ty, TyCtxt,
    },
};
use rustc_span::{
    def_id::{DefId, LocalDefId},
    DUMMY_SP,
};
use rustc_trait_selection::traits::ObligationCtxt;

/// Returns a set of all regions in a function and an iterator over there constraints
/// RegSubReg constrains relate the regions from the functions definition
/// VarSubReg/RegSubVar constrains indicate additional constraints imposed by subtyping when instantiating the function
pub(crate) fn constraints_of_fn<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: LocalDefId,
) -> (impl Iterator<Item = Region<'tcx>>, impl Iterator<Item = Constraint<'tcx>>) {
    let infcx = tcx.infer_ctxt().build();

    // identitity fn ty and sig
    let fn_sig: EarlyBinder<Binder<FnSig>> = tcx.fn_sig(def_id);
    let fn_sig = fn_sig.subst_identity();

    let eb_regions = InternalSubsts::identity_for_item(tcx, def_id).regions();
    let lb_regions = fn_sig.bound_vars().iter().filter_map(move |x| match x {
        BoundVariableKind::Region(r) => Some(Region::new_free(tcx, def_id.to_def_id(), r)),
        _ => None,
    });
    let regions = eb_regions.chain(lb_regions);
    let fn_sig = tcx.liberate_late_bound_regions(def_id.to_def_id(), fn_sig);
    let fn_ty = tcx.mk_fn_ptr(Binder::dummy(fn_sig));

    // Try to call this function in a hypothetical context with the same types but where all the regions are generalized

    // generalize function type and param_env
    let fn_ty_gen = generalize(fn_ty, &infcx);
    let param_env: ParamEnv = generalize(tcx.param_env(def_id), &infcx);

    // subtyping constraints
    let ocx = ObligationCtxt::new(&infcx);
    ocx.sub(&ObligationCause::dummy(), param_env, fn_ty, fn_ty_gen).unwrap();

    let mk_obligation =
        |predicate| Obligation::new(tcx, ObligationCause::dummy(), param_env, predicate);

    // predicate constraints
    let predicates: GenericPredicates = tcx.predicates_of(def_id);
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
    let constraints = constraints.constraints.into_iter().map(move |(x, _)| x);
    (regions, constraints)
}

pub(crate) fn generalize_fn_def<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: DefId,
    infcx: &InferCtxt<'tcx>,
    subst_ref: SubstsRef<'tcx>,
) -> (Ty<'tcx>, impl Iterator<Item = (Region<'tcx>, Region<'tcx>)>) {
    let fn_ty_gen = tcx.mk_fn_def(def_id, subst_ref);
    let (fn_sig_gen, map) = tcx.replace_late_bound_regions(fn_ty_gen.fn_sig(tcx), |_| {
        infcx.next_region_var(RegionVariableOrigin::MiscVariable(DUMMY_SP))
    });
    let fn_ty_gen = tcx.mk_fn_ptr(Binder::dummy(fn_sig_gen));

    let id_subst = InternalSubsts::identity_for_item(tcx, def_id);
    let iter1 = id_subst.regions().zip(subst_ref.regions());
    let iter2 = map.into_iter().map(move |(br, reg_gen)| {
        let reg = Region::new_free(tcx, def_id, br.kind);
        (reg, reg_gen)
    });
    let iter = iter1.chain(iter2);
    (fn_ty_gen, iter)
}
