use super::{
    full_signature_logic,
    parsing::{parse_home_sig_lit, Home, HomeSig},
    region_set::RegionSet,
    typeck::MutDerefType::{Cur, Fin},
    types::*,
    util::{generalize, RegionReplacer},
};
use crate::{
    error::{CreusotResult, Error},
    util,
};
use itertools::Either;
use rustc_ast::Mutability;
use rustc_data_structures::fx::FxHashMap;
use rustc_infer::{
    infer::{
        at::ToTrace, region_constraints::Constraint, InferCtxt, RegionVariableOrigin,
        SubregionOrigin, TyCtxtInferExt, ValuePairs,
    },
    traits::ObligationCause,
};
use rustc_middle::{
    ty,
    ty::{
        error::{ExpectedFound, TypeError},
        Instance, InternalSubsts, ParamEnv, PolyFnSig, Region, RegionKind, RegionVid, SubstsRef,
        TyCtxt, TyKind, TypeFoldable, TypeVisitable, TypeVisitor,
    },
};
use rustc_span::{def_id::DefId, Span, Symbol, DUMMY_SP};
use rustc_target::abi::VariantIdx;
use rustc_trait_selection::traits::ObligationCtxt;
use std::{iter, ops::ControlFlow};

fn home_sig(ctx: &Ctx<'_>, def_id: DefId) -> CreusotResult<Option<HomeSig>> {
    let home_sig = util::get_attr_lit(ctx.tcx, def_id, &["creusot", "prusti", "home_sig"]);
    match home_sig {
        Some(home_sig) => Ok(parse_home_sig_lit(home_sig)?),
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
        SimpleCtxt { ocx: ObligationCtxt::new(infcx), param_env }
    }

    fn sub<T: ToTrace<'tcx>>(
        &self,
        span: Span,
        expected: T,
        actual: T,
    ) -> Result<(), TypeError<'tcx>> {
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

fn origin_types<'tcx>(origin: &SubregionOrigin<'tcx>) -> Option<ExpectedFound<ty::Ty<'tcx>>> {
    match origin {
        SubregionOrigin::Subtype(t) => match t.values {
            ValuePairs::Regions(_) => None,
            ValuePairs::Terms(t) => Some(ExpectedFound {
                found: t.found.ty().unwrap(),
                expected: t.expected.ty().unwrap(),
            }),
            _ => unreachable!(),
        },
        _ => unreachable!(),
    }
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
        None => (Either::Right(iter::repeat(ctx.curr_home())), ctx.curr_home()),
    };
    let infcx = tcx.infer_ctxt().build();
    let ocx = SimpleCtxt::new(&infcx, ctx.param_env());
    let subst_ref = generalize(subst_ref, &infcx);
    let (fn_ty_gen, iter) = super::variance::generalize_fn_def(tcx, def_id, &infcx, subst_ref);

    let mut subst_map: SubstMap = iter.collect();

    // map sub-typing obligations back to there cause
    let mut span_map: FxHashMap<Span, Ty> = FxHashMap::default();

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
        span_map.insert(span, ty);
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
            let span = origin.span();
            curr_ok = match origin_types(origin) {
                None => {
                    let ty = span_map[&span];
                    assert_eq!(ty.home, reg);
                    check_move_ts(ts, ctx, ty, span).map_err(|e|
                        e.add_msg(format_args!("\nrequired by function call")))
                },
                Some(x) => {
                    let found = prepare_display(x.found, ctx);
                    let replacer = |r: Region<'tcx>| match r.kind() {
                        RegionKind::ReVar(vid2) if vid2 == vid => make_region_for_display(ts, ctx),
                        _ => r
                    };
                    let reg = DisplayRegion(reg, ctx);
                    let dts = DisplayRegion(ts, ctx);
                    let expected = x.expected.fold_with(&mut RegionReplacer{f: replacer, tcx});
                    let msg = format!("the expression's lifetime `{reg}` must match the current time slice `{dts}` (found `{found}`, expected `{expected}`)");
                    Err(Error::new(span, msg))
                }
            };
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
    variant: VariantIdx,
) -> CreusotResult<Ty<'tcx>> {
    let tcx = ctx.tcx;
    // Eagerly evaluate args to avoid running multiple inference contexts at the same time
    let fields = fields.collect::<CreusotResult<Vec<_>>>()?.into_iter();
    let infcx = tcx.infer_ctxt().build();
    let ocx = SimpleCtxt::new(&infcx, ctx.param_env());

    let ty_gen = generalize(Ty::with_absurd_home(target_ty, tcx), &infcx);
    let fields_gen = ty_gen.as_adt_variant(variant, tcx);

    fields.zip(fields_gen).try_for_each(|((ty, span), ty_gen)| sup_tys(&ocx, span, ty_gen, ty))?;

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
                match origin_types(&origin) {
                    None => check_move_ts(reg2, ctx, actual, span).map_err(|e|
                    e.add_msg(format_args!("\nrequired by return type"))),
                    Some(t) => {
                        let (reg1, reg2) = (DisplayRegion(reg1, ctx), DisplayRegion(reg2, ctx));
                        let expected = prepare_display(t.expected, ctx);
                        let found = prepare_display(t.found, ctx);
                        let msg = format!("function was supposed to return data with type `{expected}` but it is returning data with type `{found}`\n\
                            expected `{reg2}` found `{reg1}`");
                        Err(Error::new(origin.span(), msg))
                    }
                }
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

struct AllRegionsOutliveCheck<'a, 'tcx> {
    ctx: &'a Ctx<'tcx>,
    ts: RegionSet,
}

impl<'a, 'tcx> TypeVisitor<TyCtxt<'tcx>> for AllRegionsOutliveCheck<'a, 'tcx> {
    type BreakTy = Region<'tcx>;

    fn visit_region(&mut self, r: Region<'tcx>) -> ControlFlow<Self::BreakTy> {
        if self.ctx.relation.outlived_by(self.ts, r.into()) {
            ControlFlow::Continue(())
        } else {
            ControlFlow::Break(r)
        }
    }
}

pub(crate) fn check_move_ts<'tcx>(
    ts: Region<'tcx>,
    ctx: &Ctx<'tcx>,
    ty: Ty<'tcx>,
    span: Span,
) -> CreusotResult<()> {
    let dty = prepare_display(ty, ctx);
    let dts = prepare_display(ts, ctx);
    if ty.has_home_at_ts(ts) {
        Ok(())
    } else if !ty.ty.is_copy_modulo_regions(ctx.tcx, ctx.param_env()) {
        Err(Error::new(span, format!("{dty} cannot be moved to {dts} since it isn't copy")))
    } else if let ControlFlow::Break(r) =
        ty.ty.visit_with(&mut AllRegionsOutliveCheck { ctx, ts: ts.into() })
    {
        let r = prepare_display(r, ctx);
        Err(Error::new(span, format!("{dty} cannot be moved to {dts} since it doesn't live long enough\n{r} doesn't outlive {dts}")))
    } else if !ctx.relation.outlives(ts.into(), ty.home.into()) {
        Err(Error::new(
            span,
            format!("{dty} cannot be moved to {dts} since it didn't exist at that point"),
        ))
    } else {
        Ok(())
    }
}

pub(crate) fn check_move_ts_with_old<'tcx>(
    ts: Region<'tcx>,
    ctx: &Ctx<'tcx>,
    ty: Ty<'tcx>,
    span: Span,
    old_ts: Option<Region<'tcx>>,
) -> CreusotResult<()> {
    check_move_ts(ts, ctx, Ty{ty: ty.ty, home: old_ts.unwrap_or(ty.home)}, span)
}

pub(crate) enum MutDerefType {
    Cur,
    Fin,
}

pub(crate) fn mut_deref<'tcx>(
    ts: Region<'tcx>,
    ctx: &Ctx<'tcx>,
    ty: Ty<'tcx>,
    span: Span,
) -> CreusotResult<(MutDerefType, Ty<'tcx>)> {
    let Some((end, nty, Mutability::Mut)) = ty.as_ref(ts) else {unreachable!()};
    match ts {
        ts if ty.has_home_at_ts(ts) => Ok((Cur, nty)),
        ts if sub_ts(end, ts) => Ok((Fin, nty)),
        _ => {
            let home = DisplayRegion(ty.home, &ctx);
            let end = DisplayRegion(end, &ctx);
            let ts = DisplayRegion(ts, &ctx);
            return Err(Error::new(span, format!("invalid mut dereference of expression with home `{home}` and lifetime `{end}` at time-slice `{ts}`")));
        }
    }
}

pub(crate) fn shr_deref<'tcx>(
    ts: Region<'tcx>,
    ctx: &Ctx<'tcx>,
    ty: Ty<'tcx>,
    span: Span,
) -> CreusotResult<Ty<'tcx>> {
    let Some((end, nty, Mutability::Not)) = ty.as_ref(ts) else {unreachable!()};
    // if ts has it's home in the current state we should know it's lifetime is longer than it's home
    if ts == ty.home
        || (ctx.relation.outlives(ts.into(), ty.home.into())
            && ctx.relation.outlived_by(ts.into(), end.into()))
    {
        Ok(nty)
    } else {
        let home = DisplayRegion(ty.home, &ctx);
        let end = DisplayRegion(end, &ctx);
        let ts = DisplayRegion(ts, &ctx);
        return Err(Error::new(span, format!("invalid shr dereference of expression with home `{home}` and lifetime `{end}` at time-slice `{ts}`")));
    }
}

pub(crate) fn box_deref<'tcx>(
    ts: Region<'tcx>,
    ctx: &Ctx<'tcx>,
    ty: Ty<'tcx>,
    span: Span,
) -> CreusotResult<Ty<'tcx>> {
    if ty.has_home_at_ts(ts) {
        Ok(ty.try_unbox().unwrap())
    } else {
        let home = DisplayRegion(ty.home, &ctx);
        let ts = DisplayRegion(ts, &ctx);
        Err(Error::new(
            span,
            format!(
                "invalid box dereference of expression with home `{home}` at time-slice `{ts}`"
            ),
        ))
    }
}

pub(crate) fn mk_ref<'tcx>(
    ts: Region<'tcx>,
    lft: Region<'tcx>,
    ctx: &Ctx<'tcx>,
    ty: Ty<'tcx>,
    span: Span,
) -> CreusotResult<Ty<'tcx>> {
    check_move_ts(ts, ctx, ty, span)
        .map_err(|e| e.add_msg(format_args!("\nrequired by creating reference")))?;
    Ok(Ty::make_ref(lft, ty, ctx.tcx))
}

pub(crate) fn check_signature_agreement<'tcx>(
    tcx: TyCtxt<'tcx>,
    impl_id: DefId,
    trait_id: DefId,
    refn_subst: SubstsRef<'tcx>,
) -> CreusotResult<()> {
    use rustc_ast::{token, MetaItemLit as Lit};
    let trait_home_sig = util::get_attr_lit(tcx, trait_id, &["creusot", "prusti", "home_sig"]);
    let Some(trait_home_sig) = trait_home_sig else {
        return Ok(()); // We're not specializing a home signature
    };
    let impl_id_subst = InternalSubsts::identity_for_item(tcx, impl_id);
    let impl_span: Span = tcx.def_span(impl_id);
    let ts = Lit::from_token_lit(
        token::Lit { kind: token::Err, symbol: Symbol::intern("curr"), suffix: None },
        impl_span,
    );
    let ts = ts.ok().unwrap();

    let sig = tcx.fn_sig(trait_id).subst(tcx, refn_subst);
    let (ctx, ts, arg_tys, (_, expect_res_ty)) =
        full_signature_logic::<Vec<_>>(tcx, trait_home_sig, sig, &ts, trait_id)?;
    let args = arg_tys.into_iter().map(|(_, (_,  ty))| Ok((ty, impl_span)));
    let actual_res_ty = check_call(&ctx, ts, impl_id, impl_id_subst, args)?;
    check_sup(&ctx, expect_res_ty, actual_res_ty, impl_span)
}
