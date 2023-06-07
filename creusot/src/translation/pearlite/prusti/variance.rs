use rustc_infer::infer::{InferCtxt, RegionVariableOrigin, TyCtxtInferExt};
use rustc_infer::infer::outlives::env::OutlivesEnvironment;
use rustc_infer::traits::Obligation;
use rustc_middle::traits::ObligationCause;
use rustc_middle::ty::{
    SubstsRef, Ty, Binder, GenericParamDefKind, GenericPredicates, InternalSubsts, ParamEnv,
    PredicateKind, Region, RegionKind, TyCtxt,
};
use rustc_span::{
    def_id::{DefId, LocalDefId},
    DUMMY_SP,
};
use rustc_infer::infer::DefineOpaqueTypes::No as DefOpaque;
use rustc_trait_selection::traits::ObligationCtxt;
use rustc_trait_selection::traits::outlives_bounds::InferCtxtExt;

pub(crate) fn empty_regions(
    tcx: TyCtxt<'_>,
    def_id: LocalDefId,
) -> impl Iterator<Item = Region<'_>> {
    let infcx = tcx.infer_ctxt().build();
    let param_env: ParamEnv = tcx.param_env(def_id);
    // identitity fn ty and sig
    let fn_sig = tcx.fn_sig(def_id).subst_identity();
    let fn_sig = tcx.liberate_late_bound_regions(def_id.to_def_id(), fn_sig);
    let fn_ty = tcx.mk_fn_ptr(Binder::dummy(fn_sig));
    // generalized fn ty and sig
    let subst_ref =
        InternalSubsts::for_item(infcx.tcx, def_id.to_def_id(), |param, _| match param.kind {
            GenericParamDefKind::Lifetime => infcx.var_for_def(DUMMY_SP, param),
            // Needed to handle case where a function has an unused type parameter
            _ => tcx.mk_param_from_def(param),
        });
    let (fn_ty_gen, iter) = generalize_fn_def(tcx, def_id.to_def_id(), &infcx, subst_ref);

    // subtyping constraints
    let ocx = ObligationCtxt::new(&infcx);
    let infer_ok =
        infcx.at(&ObligationCause::dummy(), param_env).sub( DefOpaque,fn_ty_gen, fn_ty).unwrap();
    ocx.register_infer_ok_obligations(infer_ok);
    let mk_obligation =
        |predicate| Obligation::new(tcx, ObligationCause::dummy(), param_env, predicate);

    // predicate constraints
    let predicates: GenericPredicates = tcx.predicates_of(def_id);
    let predicates = predicates.instantiate(tcx, subst_ref).predicates;
    let obligations = predicates.into_iter().map(mk_obligation);
    ocx.register_obligations(obligations);

    // well formedness constraints
    ocx.register_obligation(mk_obligation(
        tcx.mk_predicate(Binder::dummy(PredicateKind::WellFormed(fn_ty_gen.into()))),
    ));
    let wf_tys = ocx.assumed_wf_types(param_env, DUMMY_SP, def_id);
    assert!(ocx.select_all_or_error().is_empty());

    let implied_bounds = infcx.implied_bounds_tys(param_env, def_id, wf_tys);
    let outlives = OutlivesEnvironment::with_bounds(param_env, implied_bounds);
    ocx.resolve_regions_and_report_errors(def_id, &outlives).
        expect("region error when checking variance");

        // resolve each region variable to see if it can be blocked
    let res =
        iter.filter_map(move |(reg, reg_gen)| match infcx.fully_resolve(reg_gen).unwrap().kind() {
            RegionKind::ReVar(_) => Some(reg),
            _ => None,
        });
    res
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
        let reg = tcx.mk_re_free(def_id, br.kind);
        (reg, reg_gen)
    });
    let iter = iter1.chain(iter2);
    (fn_ty_gen, iter)
}
