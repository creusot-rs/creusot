use super::{
    full_signature,
    parsing::{parse_home_sig_lit, Home, HomeSig},
    region_set::RegionSet,
    types::*,
};
use crate::{
    error::{CreusotResult, Error},
    util,
};

use crate::prusti::typeck::MutDerefType::{Cur, Fin};
use rustc_data_structures::fx::FxHashMap;
use rustc_infer::{
    infer::{
        region_constraints::Constraint, InferCtxt, RegionVariableOrigin, SubregionOrigin,
        TyCtxtInferExt,
    },
    traits::ObligationCause,
};
use rustc_middle::{
    ty,
    ty::{
        Instance, InternalSubsts, ParamEnv, PolyFnSig, Region, RegionKind, RegionVid, SubstsRef,
        TyCtxt, TyKind, TypeFoldable,
    },
};
use rustc_span::{def_id::DefId, Span, Symbol, DUMMY_SP};
use rustc_trait_selection::traits::ObligationCtxt;
use std::iter;
use itertools::Either;
use rustc_target::abi::VariantIdx;
use rustc_infer::infer::at::ToTrace;
use rustc_middle::ty::error::TypeError;

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
    fn convert_sig_pair(
        &mut self,
        home: Home,
        ty_gen: ty::Ty<'tcx>,
        infcx: &InferCtxt<'tcx>,
    ) -> Ty<'tcx> {
        let origin = RegionVariableOrigin::MiscVariable(DUMMY_SP);
        let ty_gen = if home.is_ref { ty_gen.peel_refs() } else { ty_gen };
        let home_gen = *self.0.entry(home.data).or_insert_with(|| infcx.next_region_var(origin));
        Ty { home: home_gen, ty: ty_gen }
    }

    fn get_vid(&self, sym: Symbol) -> Option<RegionVid> {
        match self.0.get(&sym)?.kind() {
            RegionKind::ReVar(vid) => Some(vid),
            _ => unreachable!(),
        }
    }
}

/// Maps region variables to there lower bounds
struct RegionInfo(FxHashMap<RegionVid, RegionSet>);

impl RegionInfo {
    fn new<'tcx>(
        constraints: impl Iterator<Item = (Constraint<'tcx>, SubregionOrigin<'tcx>)>,
    ) -> Self {
        let mut res = RegionInfo(FxHashMap::default());
        constraints.for_each(|(c, _)| match c {
            Constraint::RegSubVar(reg, gen) => res.add_bound(gen, reg),
            Constraint::VarSubReg(_, _) => {} // This comes from invariance which we ignore
            _ => unreachable!(),
        });
        res
    }

    fn add_bound(&mut self, key: RegionVid, val: Region<'_>) {
        let reg = self.0.entry(key).or_insert(RegionSet::EMPTY);
        *reg = reg.union(val.into())
    }

    fn get_region<'tcx>(&self, key: Region<'tcx>, tcx: TyCtxt<'tcx>) -> Region<'tcx> {
        match key.kind() {
            RegionKind::ReVar(vid) => {
                let reg = *self.0.get(&vid).unwrap_or(&RegionSet::EMPTY);
                reg.into_region(tcx)
            }
            _ => unreachable!(),
        }
    }
}

struct SimpleCtxt<'a, 'tcx> {
    ocx: ObligationCtxt<'a, 'tcx>,
    param_env: ParamEnv<'tcx>,
}

impl<'a, 'tcx> SimpleCtxt<'a, 'tcx> {
    fn new(infcx: &'a InferCtxt<'tcx>, param_env: ParamEnv<'tcx>) -> Self {
        SimpleCtxt{ocx: ObligationCtxt::new(infcx), param_env}
    }

    fn sub<T: ToTrace<'tcx>>(&self, span: Span, expected: T, actual: T) -> Result<(), TypeError<'tcx>> {
        self.ocx.sub(&ObligationCause::dummy_with_span(span), self.param_env, expected, actual)
    }

    fn normalize<T: TypeFoldable<TyCtxt<'tcx>>>(&self, t: T) -> T {
        self.ocx.normalize(&ObligationCause::dummy(), self.param_env, t)
    }

    fn infcx(&self) -> &'a InferCtxt<'tcx> {
        self.ocx.infcx
    }

    fn tcx(&self) -> TyCtxt<'tcx> {
        self.infcx().tcx
    }
}


fn sup_tys<'tcx>(
    ctx: &SimpleCtxt<'_, 'tcx>,
    span: Span,
    ty_gen: Ty<'tcx>,
    ty: Ty<'tcx>,
) -> CreusotResult<()> {
    if ty.is_never() {
        return Ok(()); // Don't generate constraints for the never type
    }
    let Ty { ty: ty_gen, home: home_gen } = ctx.normalize(ty_gen);
    let Ty { ty, home } = ctx.normalize(ty);
    ctx.sub(span, home_gen, home).unwrap();
    match ctx.sub(span, ty_gen, ty) {
        Ok(x) => x,
        Err(err) => return Err(Error::new(span, err.to_string(ctx.tcx()))),
    };
    Ok(())
}

fn generalize<'tcx, T: TypeFoldable<TyCtxt<'tcx>>>(t: T, infcx: &InferCtxt<'tcx>) -> T {
    t.fold_with(&mut RegionReplacer {
        tcx: infcx.tcx,
        f: |_| infcx.next_region_var(RegionVariableOrigin::MiscVariable(DUMMY_SP)),
    })
}

pub(crate) fn check_call<'tcx>(
    ctx: &Ctx<'tcx>,
    ts: Region<'tcx>,
    def_id: DefId,
    subst_ref: SubstsRef<'tcx>,
    args: impl Iterator<Item = CreusotResult<(Ty<'tcx>, Span)>>,
) -> CreusotResult<Ty<'tcx>> {
    let tcx = ctx.tcx;
    // Eagerly evaluate args to avoid running multiple inference contexts at the same time
    let args = args.collect::<CreusotResult<Vec<_>>>()?.into_iter();
    let (home_sig_args, home_sig_res) = match home_sig(ctx, def_id)? {
        Some((args, res)) => (Either::Left(args.into_iter()), res),
        None => {
            (Either::Right(iter::repeat(ctx.curr_home())), ctx.curr_home())
        },
    };
    let infcx = tcx.infer_ctxt().build();
    let ocx = SimpleCtxt::new(&infcx, ctx.param_env());
    let subst_ref = generalize(subst_ref, &infcx);
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
    args.zip(args_gen).zip(home_sig_args).try_for_each(|((arg, &ty_gen), home_sig_arg)| {
        let (ty, span) = arg;

        let ty_gen = subst_map.convert_sig_pair(home_sig_arg, ty_gen, &infcx);
        sup_tys(&ocx, span, ty_gen, ty)
    })?;
    let res_ty_gen = subst_map.convert_sig_pair(home_sig_res, res_ty_gen, &infcx);
    // let outlives = OutlivesEnvironment::new(param_env);
    // infcx.process_registered_region_obligations(&outlives);
    let constraints = infcx.take_and_reset_region_constraints();
    let iter = constraints.constraints.into_iter();
    let curr_vid = subst_map.get_vid(ctx.curr_sym);
    let mut curr_ok = Ok(());
    let iter = iter.inspect(|(c, origin)| match (*c, curr_vid) {
        (Constraint::RegSubVar(reg, var), Some(vid))
            if var == vid && curr_ok.is_ok() && !sub_ts(reg, ts) =>
        {
            let reg = DisplayRegion(reg, ctx);
            let ts = DisplayRegion(ts, ctx);
            curr_ok = Err(Error::new(
                origin.span(),
                format!("`{reg}` must match the current time slice `{ts}`"),
            ))
        }
        _ => {}
    });
    let var_info = RegionInfo::new(iter);
    curr_ok?;

    let res = res_ty_gen.fold_with(&mut RegionReplacer { tcx, f: |r| var_info.get_region(r, tcx) });
    Ok(res)
}

pub(crate) fn check_constructor<'tcx>(
    ctx: &Ctx<'tcx>,
    fields: impl Iterator<Item = CreusotResult<(Ty<'tcx>, Span)>>,
    target_ty: ty::Ty<'tcx>,
    variant: VariantIdx
) -> CreusotResult<Ty<'tcx>> {
    let tcx = ctx.tcx;
    // Eagerly evaluate args to avoid running multiple inference contexts at the same time
    let fields = fields.collect::<CreusotResult<Vec<_>>>()?.into_iter();
    let infcx = tcx.infer_ctxt().build();
    let ocx = SimpleCtxt::new(&infcx, ctx.param_env());

    let ty_gen = generalize(Ty::with_absurd_home(target_ty, tcx), &infcx);
    let fields_gen = ty_gen.as_adt_variant(variant, tcx);

    fields.zip(fields_gen).try_for_each(|((ty, span), ty_gen)| {
        sup_tys(&ocx, span, ty_gen, ty)
    })?;

    let constraints = infcx.take_and_reset_region_constraints();
    let var_info = RegionInfo::new(constraints.constraints.into_iter());
    Ok(ty_gen.fold_with(&mut RegionReplacer { tcx, f: |r| var_info.get_region(r, tcx) }))
}

pub(crate) fn union<'tcx>(
    ctx: &Ctx<'tcx>,
    target: ty::Ty<'tcx>,
    elts: impl Iterator<Item = CreusotResult<Ty<'tcx>>>,
) -> CreusotResult<Ty<'tcx>> {
    // Eagerly evaluate args to avoid running multiple inference contexts at the same time
    let mut elts = elts.collect::<CreusotResult<Vec<_>>>()?.into_iter();
    let tcx = ctx.tcx;
    let infcx = tcx.infer_ctxt().build();
    let ocx = SimpleCtxt::new(&infcx, ctx.param_env());
    let ty_gen = target.fold_with(&mut RegionReplacer {
        tcx,
        f: |_| infcx.next_region_var(RegionVariableOrigin::MiscVariable(DUMMY_SP)),
    });
    let home_gen = infcx.next_region_var(RegionVariableOrigin::MiscVariable(DUMMY_SP));
    let ty_gen = Ty { ty: ty_gen, home: home_gen };
    elts.try_for_each(|ty| sup_tys(&ocx, DUMMY_SP, ty_gen, ty))?;
    let constraints = infcx.take_and_reset_region_constraints();
    let var_info = RegionInfo::new(constraints.constraints.into_iter());
    let res = ty_gen.fold_with(&mut RegionReplacer { tcx, f: |r| var_info.get_region(r, tcx) });
    Ok(res)
}

pub(crate) fn check_sup<'tcx>(
    ctx: &Ctx<'tcx>,
    expected: Ty<'tcx>,
    actual: Ty<'tcx>,
    span: Span,
) -> CreusotResult<()> {
    let tcx = ctx.tcx;
    let infcx = tcx.infer_ctxt().build();
    let ocx = SimpleCtxt::new(&infcx, ctx.param_env());
    sup_tys(&ocx, span, expected, actual)?;
    let constraints = infcx.take_and_reset_region_constraints();
    constraints.constraints.into_iter().try_for_each(|(c, origin)| match c {
        Constraint::RegSubReg(reg1, reg2) => {
            if sub_ts(reg1, reg2) {
                Ok(())
            } else {
                let (reg1, reg2) = (DisplayRegion(reg1, ctx), DisplayRegion(reg2, ctx));
                Err(Error::new(origin.span(),format!("function was supposed to return data with home/lifetime `{reg2}` but it is returning data with home/lifetime `{reg1}`")))
            }
        }
        _ => Ok(()),
    })
}

pub(crate) fn try_resolve<'tcx>(
    ctx: &Ctx<'tcx>,
    def_id: DefId,
    subst: SubstsRef<'tcx>,
) -> (DefId, SubstsRef<'tcx>) {
    match Instance::resolve(ctx.tcx, ctx.param_env(), def_id, subst) {
        Err(_) | Ok(None) => return (def_id, subst), // Can't specialize
        Ok(Some(inst)) => (inst.def.def_id(), inst.substs),
    }
}

pub(crate) enum MutDerefType {
    Cur,
    Fin,
}

pub(crate) fn check_mut_deref<'tcx>(
    ts: Region<'tcx>,
    ctx: &Ctx<'tcx>,
    ty: Ty<'tcx>,
    end: Region<'tcx>,
    span: Span,
) -> CreusotResult<MutDerefType> {
    match ts {
        ts if ty.has_home_at_ts(ts) => Ok(Cur),
        ts if sub_ts(end, ts) => Ok(Fin),
        _ => {
            let home = DisplayRegion(ty.home, &ctx);
            let end = DisplayRegion(end, &ctx);
            let ts = DisplayRegion(ts, &ctx);
            return Err(Error::new(span, format!("invalid dereference of expression with home `{home}` and lifetime `{end}` at time-slice `{ts}`")));
        }
    }
}

pub(crate) fn check_signature_agreement<'tcx>(
    tcx: TyCtxt<'tcx>,
    impl_id: DefId,
    trait_id: DefId,
    refn_subst: SubstsRef<'tcx>,
) -> CreusotResult<()> {
    use rustc_ast::{token, MetaItemLit as Lit};
    let trait_home_sig = util::get_attr_lit(tcx, trait_id, &["creusot", "prusti", "home_sig"]);
    if trait_home_sig.is_none() {
        return Ok(()); // We're not specializing a home signature
    }
    let mut ctx = Ctx::new(tcx, impl_id, true);
    let impl_id_subst = InternalSubsts::identity_for_item(tcx, impl_id);
    let impl_span: Span = tcx.def_span(impl_id);
    let ts = Lit::from_token_lit(
        token::Lit { kind: token::Err, symbol: Symbol::intern("curr"), suffix: None },
        impl_span,
    );
    let ts = ts.ok().unwrap();

    let sig = tcx.fn_sig(trait_id).subst(tcx, refn_subst);
    let (ts, arg_tys, expect_res_ty) =
        full_signature(trait_home_sig, sig, &ts, trait_id, &mut ctx)?;
    let args = arg_tys
        .zip(iter::repeat(impl_span))
        .map(|((_, ty), sp)| ty.map(|ty| (ty, sp)));
    let args = args.collect::<Vec<_>>().into_iter();
    let actual_res_ty = check_call(&ctx, ts, impl_id, impl_id_subst, args)?;
    check_sup(&ctx, expect_res_ty, actual_res_ty, impl_span)
}
