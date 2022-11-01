use super::{
    parsing::{parse_home_sig_lit, Home, HomeSig},
    types::*,
};
use crate::{
    error::{CreusotResult, Error},
    util,
};
use creusot_rustc::{
    data_structures::fx::FxHashMap,
    infer::{
        infer::{
            outlives::env::OutlivesEnvironment, region_constraints::Constraint, InferCtxt,
            RegionVariableOrigin, SubregionOrigin, TyCtxtInferExt,
        },
        traits::ObligationCause,
    },
    middle::{
        ty,
        ty::{
            EarlyBinder, Instance, InternalSubsts, ParamEnv, PolyFnSig, PredicateKind, Region,
            RegionKind, RegionVid, SubstsRef, TyCtxt, TyKind, TypeFoldable,
        },
    },
    smir::very_unstable::trait_selection::traits::query::normalize::AtExt,
    span::{def_id::DefId, Span, Symbol, DUMMY_SP},
};
use std::{collections::hash_map::Entry, iter};

fn home_sig(ctx: &Ctx<'_>, def_id: DefId) -> CreusotResult<Option<HomeSig>> {
    let home_sig = util::get_attr_lit(ctx.tcx, def_id, &["creusot", "prusti", "home_sig"]);
    match home_sig {
        Some(home_sig) => Ok(Some(parse_home_sig_lit(home_sig)?)),
        None => Ok(None),
    }
}

/// Maps lifetime/home symbols used in the signature of the function being called
/// to the region variables representing them
struct SubstMap<'tcx>(FxHashMap<Symbol, Region<'tcx>>);

impl<'tcx> FromIterator<(Region<'tcx>, Region<'tcx>)> for SubstMap<'tcx> {
    fn from_iter<T: IntoIterator<Item = (Region<'tcx>, Region<'tcx>)>>(iter: T) -> Self {
        let el_name = Symbol::intern("'_");
        let inner = iter
            .into_iter()
            .filter_map(|(k, v): (Region, Region)| {
                assert!(v.is_var());
                match k.get_name() {
                    Some(name) if name != el_name => Some((name, v)),
                    _ => None, // Ignore elided regions
                }
            })
            .collect();
        SubstMap(inner)
    }
}

impl<'tcx> SubstMap<'tcx> {
    // Convert a home from the home_signature of to a region var
    fn convert_sig_home(&mut self, sig_home: Home, infcx: &InferCtxt<'_, 'tcx>) -> Region<'tcx> {
        *self
            .0
            .entry(sig_home)
            .or_insert_with(|| infcx.next_region_var(RegionVariableOrigin::MiscVariable(DUMMY_SP)))
    }

    fn get_vid(&self, sym: Symbol) -> Option<RegionVid> {
        match self.0.get(&sym)?.kind() {
            RegionKind::ReVar(vid) => Some(vid),
            _ => unreachable!(),
        }
    }
}

/// Maps region variables to there lower bounds
struct RegionInfo<'tcx>(FxHashMap<RegionVid, Region<'tcx>>);

impl<'tcx> RegionInfo<'tcx> {
    fn new(
        constraints: impl Iterator<Item = (Constraint<'tcx>, SubregionOrigin<'tcx>)>,
        tcx: TyCtxt<'tcx>,
    ) -> Self {
        let mut res = RegionInfo(FxHashMap::default());
        constraints.for_each(|(c, _)| match c {
            Constraint::RegSubVar(reg, gen) => res.add_bound(gen, reg, tcx),
            Constraint::VarSubReg(_, _) => {} // This comes from invariance which we ignore
            _ => unreachable!(),
        });
        res
    }

    fn add_bound(&mut self, key: RegionVid, val: Region<'tcx>, tcx: TyCtxt<'tcx>) {
        match self.0.entry(key) {
            Entry::Occupied(mut occ) if !sub_ts(val, *occ.get()) => {
                occ.insert(tcx.lifetimes.re_erased);
            }
            Entry::Vacant(vac) if !sub_ts(val, tcx.lifetimes.re_static) => {
                vac.insert(val);
            }
            _ => {}
        }
    }

    fn get_region(&self, key: Region<'tcx>, tcx: TyCtxt<'tcx>) -> Region<'tcx> {
        match key.kind() {
            RegionKind::ReStatic | RegionKind::ReErased => key,
            RegionKind::ReVar(vid) => match self.0.get(&vid) {
                None => tcx.lifetimes.re_static,
                Some(r) => *r,
            },
            _ => unreachable!(),
        }
    }
}

fn sup_tys<'tcx>(
    infcx: &InferCtxt<'_, 'tcx>,
    param_env: ParamEnv<'tcx>,
    span: Span,
    ty_gen: Ty<'tcx>,
    ty: Ty<'tcx>,
) {
    if ty.is_never() {
        return; // Don't generate constraints for the never type
    }
    let oc = ObligationCause::dummy_with_span(span);
    let normalize = |ty| {
        let n_ty = infcx.at(&oc, param_env).normalize(ty).unwrap();
        let trivial = n_ty.obligations.iter().all(|ob| match ob.predicate.kind().skip_binder() {
            PredicateKind::RegionOutlives(r) if r.0 == r.1 => true,
            _ => false,
        });
        if !trivial {
            dbg!(ty);
            dbg!(n_ty.value);
            dbg!(n_ty.obligations);
            panic!();
        }
        n_ty.value
    };
    let Ty { ty: ty_gen, home: home_gen } = normalize(ty_gen);
    let Ty { ty, home } = normalize(ty);
    let infer_ok = infcx.at(&oc, param_env).sup(home_gen, home).unwrap();
    debug_assert!(infer_ok.obligations.is_empty());
    let infer_ok = match infcx.at(&oc, param_env).sub(ty_gen, ty) {
        Ok(x) => x,
        Err(err) => panic!("{:#?}", (err, ty_gen, ty, param_env)),
    };
    debug_assert!(infer_ok.obligations.is_empty());
}

/// Returns Ok(Some(ty)) if fn_ty has a "home signature" and the call can be type checked to ty
/// Ok(None) if fn_ty doesn't have a "home signature" or
/// Err(err) if there is an error while type checking or one is propagated from an argument
pub(super) fn check_call<'tcx>(
    ctx: &Ctx<'tcx>,
    ts: Region<'tcx>,
    def_id: DefId,
    subst_ref: SubstsRef<'tcx>,
    args: impl Iterator<Item = CreusotResult<(Ty<'tcx>, Span)>>,
) -> CreusotResult<Option<Ty<'tcx>>> {
    let tcx = ctx.tcx;
    // Eagerly evaluate args to avoid running multiple inference contexts at the same time
    let args = args.collect::<CreusotResult<Vec<_>>>()?.into_iter();
    let (home_sig_args, home_sig_res) = match home_sig(ctx, def_id)? {
        Some(x) => x,
        None => return Ok(None),
    };
    tcx.infer_ctxt().enter(|infcx: InferCtxt| {
        let subst_ref: SubstsRef = subst_ref.fold_with(&mut RegionReplacer {
            tcx,
            f: |_| infcx.next_region_var(RegionVariableOrigin::MiscVariable(DUMMY_SP)),
        });
        let param_env = ctx.param_env();
        let (fn_ty_gen, iter) = super::variance::generalize_fn_def(tcx, def_id, &infcx, subst_ref);

        let mut subst_map: SubstMap = iter.collect();

        let (args_gen, res_ty_gen) = match fn_ty_gen.kind() {
            TyKind::FnPtr(bind) => {
                let bind: &PolyFnSig = bind;
                let sig = bind.no_bound_vars().unwrap();
                (sig.inputs(), sig.output())
            }
            _ => unreachable!(),
        };
        args.zip(args_gen).zip(home_sig_args).for_each(|((arg, &ty_gen), home_sig_arg)| {
            let (ty, span) = arg;

            let home_gen = subst_map.convert_sig_home(home_sig_arg, &infcx);
            let ty_gen = Ty { ty: ty_gen, home: home_gen };
            sup_tys(&infcx, param_env, span, ty_gen, ty);
        });
        let res_home_gen = subst_map.convert_sig_home(home_sig_res, &infcx);
        let res_ty_gen = Ty { ty: res_ty_gen, home: res_home_gen };

        let outlives = OutlivesEnvironment::new(param_env);
        infcx.process_registered_region_obligations(outlives.region_bound_pairs(), param_env);
        let constraints = infcx.take_and_reset_region_constraints();
        let iter = constraints.constraints.into_iter();
        let curr_vid = subst_map.get_vid(ctx.curr_sym);
        let mut curr_ok = Ok(());
        let iter = iter.inspect(|(c, origin)| match (*c, curr_vid) {
            (Constraint::RegSubVar(reg, var), Some(vid))
                if var == vid && curr_ok.is_ok() && !sub_ts(reg, ts) =>
            {
                let reg = DisplayRegion(reg);
                curr_ok = Err(Error::new(
                    origin.span(),
                    format!("`{reg}` must match the current time slice"),
                ))
            }
            _ => {}
        });
        let var_info = RegionInfo::new(iter, tcx);
        curr_ok?;

        let res =
            res_ty_gen.fold_with(&mut RegionReplacer { tcx, f: |r| var_info.get_region(r, tcx) });
        Ok(Some(res))
    })
}

pub(super) fn union<'tcx>(
    ctx: &Ctx<'tcx>,
    target: ty::Ty<'tcx>,
    elts: impl Iterator<Item = CreusotResult<Ty<'tcx>>>,
) -> CreusotResult<Ty<'tcx>> {
    // Eagerly evaluate args to avoid running multiple inference contexts at the same time
    let elts = elts.collect::<CreusotResult<Vec<_>>>()?.into_iter();
    let tcx = ctx.tcx;
    let param_env = ctx.param_env();
    tcx.infer_ctxt().enter(|infcx| {
        let ty_gen = target.fold_with(&mut RegionReplacer {
            tcx,
            f: |_| infcx.next_region_var(RegionVariableOrigin::MiscVariable(DUMMY_SP)),
        });
        let home_gen = infcx.next_region_var(RegionVariableOrigin::MiscVariable(DUMMY_SP));
        let ty_gen = Ty { ty: ty_gen, home: home_gen };
        elts.for_each(|ty| {
            sup_tys(&infcx, param_env, DUMMY_SP, ty_gen, ty);
        });
        let constraints = infcx.take_and_reset_region_constraints();
        let var_info = RegionInfo::new(constraints.constraints.into_iter(), tcx);
        let res = ty_gen.fold_with(&mut RegionReplacer { tcx, f: |r| var_info.get_region(r, tcx) });
        Ok(res)
    })
}

pub(super) fn check_sup<'tcx>(
    ctx: &Ctx<'tcx>,
    expected: Ty<'tcx>,
    actual: Ty<'tcx>,
    span: Span,
) -> CreusotResult<()> {
    let tcx = ctx.tcx;
    let param_env = ctx.param_env();
    tcx.infer_ctxt().enter(|infcx| {
        sup_tys(&infcx, param_env, span, expected, actual);
        let constraints = infcx.take_and_reset_region_constraints();
        constraints.constraints.into_iter().try_for_each(|(c, origin)| match c {
            Constraint::RegSubReg(reg1, reg2) => {
                if sub_ts(reg1, reg2) {
                    Ok(())
                } else {
                    let (reg1, reg2) = (DisplayRegion(reg1), DisplayRegion(reg2));
                    Err(Error::new(origin.span(),format!("function was supposed to return data with home/lifetime `{reg2}` but it is returning data with home/lifetime `{reg1}`")))
                }
            }
            _ => unreachable!(),
        })
    })
}

pub(super) fn try_resolve<'tcx>(
    ctx: &Ctx<'tcx>,
    def_id: DefId,
    subst: SubstsRef<'tcx>,
) -> (DefId, SubstsRef<'tcx>) {
    match Instance::resolve(ctx.tcx, ctx.param_env(), def_id, subst) {
        Err(_) | Ok(None) => return (def_id, subst), // Can't specialize
        Ok(Some(inst)) => (inst.def.def_id(), inst.substs),
    }
}

pub(crate) fn check_signature_agreement<'tcx>(
    tcx: TyCtxt<'tcx>,
    impl_id: DefId,
    trait_id: DefId,
    refn_subst: SubstsRef<'tcx>,
) -> CreusotResult<()> {
    use creusot_rustc::ast::{token, Lit};
    let trait_home_sig = util::get_attr_lit(tcx, trait_id, &["creusot", "prusti", "home_sig"]);
    if trait_home_sig.is_none() {
        return Ok(()); // We're not specializing a home signature
    }
    let ctx = Ctx::new(tcx, impl_id, true);
    let impl_id_subst = InternalSubsts::identity_for_item(tcx, impl_id);
    let impl_span: Span = tcx.def_span(impl_id);
    let ts = Lit::from_token_lit(
        token::Lit { kind: token::Err, symbol: Symbol::intern("curr"), suffix: None },
        impl_span,
    );
    let ts = ts.ok().unwrap();
    let subst = |ty| EarlyBinder(ty).subst(tcx, refn_subst);
    let (ts, arg_tys, expect_res_ty) = super::full_signature(trait_home_sig, &ts, trait_id, &ctx)?;
    let args = arg_tys.map(|(_, ty)| subst(ty)).zip(iter::repeat(impl_span)).map(Ok);
    let expect_res_ty = subst(expect_res_ty);
    let actual_res_ty = check_call(&ctx, ts, impl_id, impl_id_subst, args)?;
    let actual_res_ty = match actual_res_ty {
        Some(ty) => ty,
        None => {
            return Err(Error::new(
                impl_span,
                format!(
                    "Expected `{}` to have a home signature as specified by the trait declaration",
                    tcx.item_name(impl_id)
                ),
            ))
        }
    };
    check_sup(&ctx, expect_res_ty, actual_res_ty, impl_span)
}
