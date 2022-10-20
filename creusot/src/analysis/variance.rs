use creusot_rustc::{
    hir::HirId,
    smir::very_unstable::{
        middle::ty::{
            Binder, FreeRegion, GenericParamDefKind, GenericPredicates, Generics, InternalSubsts,
            ParamEnv, PredicateKind, Region, RegionKind, TyCtxt,
        },
        trait_selection::{
            infer::{
                outlives::env::OutlivesEnvironment, InferCtxt, RegionVariableOrigin, TyCtxtInferExt,
            },
            traits::{outlives_bounds::InferCtxtExt, Obligation, ObligationCause, ObligationCtxt},
        },
    },
    span::{def_id::LocalDefId, DUMMY_SP},
};

pub(crate) fn empty_regions(
    tcx: TyCtxt<'_>,
    def_id: LocalDefId,
) -> impl Iterator<Item = Region<'_>> {
    tcx.infer_ctxt().enter(|infcx: InferCtxt| {
        let param_env: ParamEnv = tcx.param_env(def_id);
        // identitity fn ty and sig
        let fn_sig = tcx.liberate_late_bound_regions(def_id.to_def_id(), tcx.fn_sig(def_id));
        let fn_ty = tcx.mk_fn_ptr(Binder::dummy(fn_sig));
        // generalized fn ty and sig
        let subst_ref =
            InternalSubsts::for_item(infcx.tcx, def_id.to_def_id(), |param, _| match param.kind {
                GenericParamDefKind::Lifetime => infcx.var_for_def(DUMMY_SP, param),
                // Needed to handle case where a function has an unused type parameter
                _ => tcx.mk_param_from_def(param),
            });
        let fn_ty_gen = tcx.mk_fn_def(def_id.to_def_id(), subst_ref);
        let (fn_sig_gen, map) = tcx.replace_late_bound_regions(fn_ty_gen.fn_sig(tcx), |_| {
            infcx.next_region_var(RegionVariableOrigin::MiscVariable(DUMMY_SP))
        });
        let fn_ty_gen = tcx.mk_fn_ptr(Binder::dummy(fn_sig_gen));

        // subtyping constraints
        let ocx = ObligationCtxt::new(&infcx);
        let infer_ok =
            infcx.at(&ObligationCause::dummy(), param_env).sub(fn_ty_gen, fn_ty).unwrap();
        ocx.register_infer_ok_obligations(infer_ok);
        let mk_obligation =
            |predicate| Obligation::new(ObligationCause::dummy(), param_env, predicate);

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

        let implied_bounds = infcx.implied_bounds_tys(param_env, HirId::make_owner(def_id), wf_tys);
        let outlives = OutlivesEnvironment::with_bounds(param_env, Some(&infcx), implied_bounds);
        infcx.check_region_obligations_and_report_errors(def_id, &outlives);

        // Iterate pairs of regions and their generalized region variable
        let generics: &Generics = tcx.generics_of(def_id);
        let iter1 =
            generics.params.iter().zip(subst_ref).filter_map(move |(def, arg)| match def.kind {
                GenericParamDefKind::Lifetime => {
                    let ebr = def.to_early_bound_region_data();
                    let reg = tcx.mk_region(RegionKind::ReEarlyBound(ebr));
                    let reg_gen = arg.expect_region();
                    Some((reg, reg_gen))
                }
                _ => None,
            });
        let iter2 = map.into_iter().map(move |(br, reg_gen)| {
            let fr = FreeRegion { scope: def_id.to_def_id(), bound_region: br.kind };
            let reg = tcx.mk_region(RegionKind::ReFree(fr));
            (reg, reg_gen)
        });

        // resolve each region variable to see if it can be blocked
        let res = iter1.chain(iter2).filter_map(move |(reg, reg_gen)| {
            match infcx.fully_resolve(reg_gen).unwrap().kind() {
                RegionKind::ReVar(_) => Some(reg),
                _ => None,
            }
        });
        res.collect::<Vec<_>>().into_iter() // infer ctx can't escape
    })
}
