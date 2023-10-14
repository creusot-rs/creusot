use super::{
    full_signature_logic,
    parsing::{parse_home_sig_lit, HomeSig},
    region_set::StateSet,
    typeck::MutDerefType::{Cur, Fin},
    types::*,
    util::{generalize, RegionReplacer},
};
use crate::{
    error::{CreusotResult, Error},
    lints::PRUSTI_ZOMBIE,
    prusti::{
        ctx::{BaseCtx, CtxRef, InternedInfo},
        parsing::Outlives,
        with_static::PrettyRegionReplacer,
    },
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
    span_bug, ty,
    ty::{
        error::{ExpectedFound, TypeError},
        Instance, InternalSubsts, PolyFnSig, Region, RegionKind, RegionVid, SubstsRef, TyCtxt,
        TyKind, TypeFoldable, TypeSuperVisitable, TypeVisitable, TypeVisitor,
    },
};
use rustc_span::{def_id::DefId, Span, Symbol, DUMMY_SP};
use rustc_target::abi::VariantIdx;
use rustc_trait_selection::traits::ObligationCtxt;
use std::{collections::hash_map::Entry, iter, ops::ControlFlow};

// fn prepare_dbg<'tcx, T: TypeFoldable<TyCtxt<'tcx>>>(t: T, tcx: TyCtxt<'tcx>) -> T {
//     t.fold_with(&mut RegionReplacer {
//         tcx,
//         f: |r| dummy_region(tcx, Symbol::intern(&*format!("{r:?}"))),
//     })
// }
//
// macro_rules! dbg2 {
//     ($val:expr, $tcx:expr) => {
//         // Use of `match` here is intentional because it affects the lifetimes
//         // of temporaries - https://stackoverflow.com/a/48732525/1063961
//         match $val {
//             tmp => {
//                 ::std::eprintln!(
//                     "[{}:{}] {} = {:#?}",
//                     ::std::file!(),
//                     ::std::line!(),
//                     ::std::stringify!($val),
//                     prepare_dbg(tmp, $tcx)
//                 );
//                 tmp
//             }
//         }
//     };
// }

fn home_sig(ctx: CtxRef<'_, '_>, def_id: DefId) -> CreusotResult<Option<HomeSig>> {
    let home_sig = util::get_attr_lit(ctx.tcx, def_id, &["creusot", "prusti", "home_sig"]);
    match home_sig {
        Some(home_sig) => Ok(parse_home_sig_lit(home_sig)?),
        None => Ok(None),
    }
}

trait Captures<'tcx> {}
impl<'tcx, X> Captures<'tcx> for X {}

fn filter_elided<'tcx>(
    iter: impl Iterator<Item = (Region<'tcx>, Region<'tcx>)>,
) -> impl Iterator<Item = (Symbol, RegionVid)> + Captures<'tcx> {
    let el_name = Symbol::intern("'_");
    iter.into_iter().filter_map(move |(k, v): (Region, Region)| {
        assert!(v.is_var());
        match k.get_name() {
            Some(name) if name != el_name => Some((name, v.as_var())),
            _ => None, // Ignore elided regions
        }
    })
}

/// Maps region variables to there lower bounds
struct RegionInfo(FxHashMap<RegionVid, StateSet>);

impl RegionInfo {
    fn new<'tcx>(
        ctx: CtxRef<'_, 'tcx>,
        mut constraints: impl Iterator<Item = (Constraint<'tcx>, SubregionOrigin<'tcx>)>,
    ) -> CreusotResult<Self> {
        let mut res = RegionInfo(FxHashMap::default());
        constraints.try_for_each(|(c, origin)| {
            CreusotResult::Ok(match c {
                Constraint::VarSubReg(gen, reg) => res.add_bound(gen, reg),
                Constraint::RegSubReg(static_reg, reg) if static_reg.is_static() => {
                    check_call_region_constraint(ctx, None, ctx.static_region(), reg, &origin)?;
                }
                Constraint::RegSubVar(_, _) => {} // These comes from invariance which we ignore
                Constraint::RegSubReg(_, static_reg) if static_reg.is_static() => {}
                x => {
                    warn!("unhandled constraint {:?}", x)
                }
            })
        })?;
        Ok(res)
    }

    fn add_bound(&mut self, key: RegionVid, val: Region<'_>) {
        let reg = self.0.entry(key).or_insert(StateSet::EMPTY);
        *reg = reg.union(val.into())
    }

    fn get_region<'tcx>(&self, key: Region<'tcx>, tcx: TyCtxt<'tcx>) -> Region<'tcx> {
        let reg = *self.0.get(&key.as_var()).unwrap_or(&StateSet::EMPTY);
        reg.into_region(tcx)
    }
}

struct SimpleCtxt<'a, 'tcx> {
    ocx: ObligationCtxt<'a, 'tcx>,
    ctx: &'a BaseCtx<'a, 'tcx>,
}

impl<'a, 'tcx> SimpleCtxt<'a, 'tcx> {
    fn new(infcx: &'a InferCtxt<'tcx>, ctx: &'a BaseCtx<'a, 'tcx>) -> Self {
        SimpleCtxt { ocx: ObligationCtxt::new(infcx), ctx }
    }

    fn sup<T: ToTrace<'tcx>>(
        &self,
        span: Span,
        expected: T,
        actual: T,
    ) -> Result<(), TypeError<'tcx>> {
        self.ocx.sup(
            &ObligationCause::dummy_with_span(span),
            self.ctx.param_env(),
            expected,
            actual,
        )
    }

    fn normalize<T: TypeFoldable<TyCtxt<'tcx>>>(&self, t: T, static_r: Region<'tcx>) -> T {
        let t = super::with_static::normalize_static_replacer(self.ctx, t, static_r);
        self.ocx.normalize(&ObligationCause::dummy(), self.ctx.param_env(), t)
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
    let Ty { ty: ty_gen } = ty_gen;
    let Ty { ty } = ty;
    match ctx.sup(span, ty_gen, ty) {
        Ok(()) => (),
        Err(_) => {
            // let err = display_fold(err, ctx.ctx);
            // return Err(Error::new(span, err.to_string(ctx.tcx())))
            // Sadly this doesn't work since TypeError doesn't implement type TypeFoldable
            let ty = display_fold(ty, ctx.ctx);
            let tcx = ctx.tcx();
            let replacer = |r: Region<'tcx>| match r.kind() {
                RegionKind::ReStatic => tcx.lifetimes.re_static,
                _ => tcx.lifetimes.re_erased,
            };
            let ty_gen =
                ty_gen.fold_with(&mut PrettyRegionReplacer { f: replacer, ctx: ctx.ctx.interned });
            return Err(Error::new(span, format!("expected `{ty_gen}` found `{ty}`")));
        }
    };
    Ok(())
}

fn origin_types<'tcx>(origin: &SubregionOrigin<'tcx>) -> Option<ExpectedFound<ty::Ty<'tcx>>> {
    match origin {
        SubregionOrigin::Subtype(t) => match t.values {
            ValuePairs::Regions(_) => None,
            ValuePairs::Terms(terms) => Some(ExpectedFound {
                found: terms.found.ty().unwrap(),
                expected: terms.expected.ty().unwrap(),
            }),
            _ => unreachable!(),
        },
        _ => unreachable!(),
    }
}

pub(crate) fn check_call<'tcx>(
    ctx: CtxRef<'_, 'tcx>,
    ts: Region<'tcx>,
    def_id: DefId,
    subst_ref: SubstsRef<'tcx>,
    args: impl Iterator<Item = CreusotResult<((Region<'tcx>, Ty<'tcx>), Span)>>,
    call_span: Span,
) -> CreusotResult<Ty<'tcx>> {
    let tcx = ctx.tcx;
    // Eagerly evaluate args to avoid running multiple inference contexts at the same time
    let args = args.collect::<CreusotResult<Vec<_>>>()?.into_iter();
    let home_sig = home_sig(ctx, def_id)?;
    let (home_sig_args, home_sig_bounds) = match &home_sig {
        Some(home_sig) => (Either::Left(home_sig.args()), Either::Left(home_sig.bounds())),
        None => (Either::Right(iter::repeat(ctx.curr_home())), Either::Right(iter::empty())),
    };

    let infcx = tcx.infer_ctxt().build();
    let ocx = SimpleCtxt::new(&infcx, &*ctx);
    let subst_ref = generalize(subst_ref, &infcx);
    let (fn_ty_gen, iter) = super::variance::generalize_fn_def(tcx, def_id, &infcx, subst_ref);
    let fn_ty_gen = ocx.normalize(fn_ty_gen, tcx.lifetimes.re_static);
    let subst_iter = filter_elided(iter);

    let (args_gen, res_ty_gen) = match fn_ty_gen.kind() {
        TyKind::FnPtr(bind) => {
            let bind: &PolyFnSig = bind;
            let sig = bind.no_bound_vars().unwrap();
            (sig.inputs(), sig.output())
        }
        _ => unreachable!(),
    };

    // maps homes in the home signature to states that were passed in for them
    let mut constrained_homes = FxHashMap::default();

    for ((arg, &ty_gen), home_sig_arg) in args.zip(args_gen).zip(home_sig_args) {
        let ((from_ts, mut ty), span) = arg;
        if home_sig_arg == ctx.curr_sym {
            ty = check_move_state(from_ts, ts, ctx, ty, span)?;
        } else {
            match constrained_homes.entry(home_sig_arg) {
                Entry::Vacant(vac) => {
                    vac.insert(from_ts);
                }
                Entry::Occupied(occ) if *occ.get() != from_ts => {
                    let d_oth_ts = prepare_display(*occ.get(), ctx);
                    let d_this_ts = prepare_display(from_ts, ctx);
                    return Err(Error::new(span, format!("expected argument to come from state `{d_oth_ts}`, but it came from `{d_this_ts}`\n\
                    required by home signature of function")));
                }
                _ => {}
            }
        }

        let ty_gen = Ty { ty: ty_gen };
        sup_tys(&ocx, span, ty_gen, ty)?;
    }
    constrained_homes.insert(ctx.curr_sym, ts); // 'curr is always constrained to the current state

    // check explicit constraints
    for Outlives { long, short } in home_sig_bounds {
        if let (Some(&long), Some(&short)) =
            (constrained_homes.get(&long), constrained_homes.get(&short))
        {
            if !ctx.relation.outlives(long.into(), short.into()) {
                let dlong = prepare_display(long, ctx);
                let dshort = prepare_display(short, ctx);
                let msg = format!("expected `{dlong}` to outlive `{dshort}`\n\
                    required by home signature of function");
                return Err(Error::new(call_span, msg));
            }
        }
    }

    // maps region variables to states they must be equal to
    let constrained_vars: FxHashMap<_, _> = subst_iter
        .filter_map(|(home, var)| {
            let constraint = *constrained_homes.get(&home)?;
            Some((var, constraint))
        })
        .collect();

    let res_ty_gen = Ty { ty: res_ty_gen };
    let constraints = infcx.take_and_reset_region_constraints();
    // let outlives = OutlivesEnvironment::new(param_env);
    // infcx.process_registered_region_obligations(&outlives);

    let iter = constraints.constraints.into_iter();
    let mut curr_ok = Ok(());
    let iter = iter.filter(|(c, origin)| match *c {
        _ if curr_ok.is_err() => false,
        Constraint::VarSubReg(var, reg) => {
            if let Some(constraint) = constrained_vars.get(&var) {
                curr_ok = check_call_region_constraint(ctx, Some(var), *constraint, reg, &origin);
                false
            } else {
                true
            }
        }
        _ => true,
    });
    let var_info = RegionInfo::new(ctx, iter)?;
    curr_ok?;

    let res = res_ty_gen.fold_with(&mut RegionReplacer {
        tcx,
        f: |r| {
            if r.is_static() {
                ctx.static_region()
            } else if let Some(constraint) = constrained_vars.get(&r.as_var()) {
                *constraint
            } else {
                var_info.get_region(r, tcx)
            }
        },
    });
    if let Some(r) = ty_outlives(res, ts, ctx) {
        let dty = prepare_display(res, ctx);
        let dts = prepare_display(ts, ctx);
        let r = prepare_display(r, ctx);
        let msg = format!("`{dty}` cannot be returned in `{dts}` since it doesn't live long enough\n`{r}` doesn't outlive `{dts}`");
        return Err(Error::new(call_span, msg));
    }
    Ok(res)
}

fn check_call_region_constraint<'tcx>(
    ctx: CtxRef<'_, 'tcx>,
    vid: Option<RegionVid>,
    expected_r: Region<'tcx>,
    actual_r: Region<'tcx>,
    origin: &SubregionOrigin<'tcx>,
) -> Result<(), Error> {
    if sub_ts(actual_r, expected_r) {
        return Ok(());
    }
    let tcx = ctx.tcx;
    let span = origin.span();
    match origin_types(origin) {
        None => span_bug!(span, "bug"),
        Some(x) => {
            let found = prepare_display(x.found, ctx);
            let replacer = |r: Region<'tcx>| match r.kind() {
                RegionKind::ReVar(vid2) if Some(vid2) == vid => {
                    make_region_for_display(expected_r, ctx)
                }
                RegionKind::ReStatic => tcx.lifetimes.re_static,
                _ => tcx.lifetimes.re_erased,
            };
            let reg = prepare_display(actual_r, ctx);
            let dts = prepare_display(expected_r, ctx);
            let expected =
                x.expected.fold_with(&mut PrettyRegionReplacer { f: replacer, ctx: ctx.interned });
            let msg = format!("the expression's lifetime `{reg}` must match the current time slice `{dts}` (found `{found}`, expected `{expected}`)");
            Err(Error::new(span, msg))
        }
    }
}

pub(crate) fn check_constructor<'tcx>(
    ctx: CtxRef<'_, 'tcx>,
    fields: impl Iterator<Item = CreusotResult<(Ty<'tcx>, Span)>>,
    target_ty: ty::Ty<'tcx>,
    variant: VariantIdx,
) -> CreusotResult<Ty<'tcx>> {
    let tcx = ctx.tcx;
    // Eagerly evaluate args to avoid running multiple inference contexts at the same time
    let fields = fields.collect::<CreusotResult<Vec<_>>>()?.into_iter();
    let infcx = tcx.infer_ctxt().build();
    let ocx = SimpleCtxt::new(&infcx, &*ctx);

    let ty_gen = generalize(Ty::with_absurd_home(target_ty, tcx), &infcx);
    let fields_gen = ty_gen.as_adt_variant(variant, ctx);

    fields.zip(fields_gen).try_for_each(|((ty, span), ty_gen)| sup_tys(&ocx, span, ty_gen, ty))?;

    let constraints = infcx.take_and_reset_region_constraints();
    let var_info = RegionInfo::new(ctx, constraints.constraints.into_iter())?;
    Ok(ty_gen.fold_with(&mut RegionReplacer { tcx, f: |r| var_info.get_region(r, tcx) }))
}

pub(crate) fn union<'tcx>(
    ctx: CtxRef<'_, 'tcx>,
    target: ty::Ty<'tcx>,
    elts: impl Iterator<Item = CreusotResult<(Ty<'tcx>, Span)>>,
) -> CreusotResult<Ty<'tcx>> {
    // Eagerly evaluate args to avoid running multiple inference contexts at the same time
    let mut elts = elts.collect::<CreusotResult<Vec<_>>>()?.into_iter();
    let tcx = ctx.tcx;
    let infcx = tcx.infer_ctxt().build();
    let ocx = SimpleCtxt::new(&infcx, &*ctx);
    let ty_gen = generalize(Ty::with_absurd_home(target, tcx), &infcx);
    elts.try_for_each(|(ty, span)| sup_tys(&ocx, span, ty_gen, ty))?;
    let constraints = infcx.take_and_reset_region_constraints();
    let var_info = RegionInfo::new(ctx, constraints.constraints.into_iter())?;
    let res = ty_gen.fold_with(&mut RegionReplacer { tcx, f: |r| var_info.get_region(r, tcx) });
    Ok(res)
}

pub(super) fn normalize<'tcx, T: TypeFoldable<TyCtxt<'tcx>>>(
    ctx: &'_ BaseCtx<'_, 'tcx>,
    ty: T,
) -> T {
    let tcx = ctx.tcx;
    let infcx = tcx.infer_ctxt().build();
    let ocx = SimpleCtxt::new(&infcx, ctx);
    ocx.normalize(ty, ctx.static_region())
}

pub(crate) fn check_sup<'tcx>(
    ctx: CtxRef<'_, 'tcx>,
    expected: Ty<'tcx>,
    actual: Ty<'tcx>,
    span: Span,
) -> CreusotResult<()> {
    let tcx = ctx.tcx;
    let infcx = tcx.infer_ctxt().build();
    let ocx = SimpleCtxt::new(&infcx, &*ctx);

    // Avoid contravariant constraints
    let mut back_map = FxHashMap::default();
    let expected = expected.fold_with(&mut RegionReplacer {
        tcx,
        f: |r| {
            let res = infcx.next_region_var(RegionVariableOrigin::MiscVariable(DUMMY_SP));
            back_map.insert(res.as_var(), r);
            res
        },
    });
    sup_tys(&ocx, span, expected, actual)?;
    let constraints = infcx.take_and_reset_region_constraints();
    constraints.constraints.into_iter().try_for_each(|(c, origin)| match c {
        Constraint::VarSubReg(var, reg1) => {
            let reg2 = back_map[&var];
            if sub_ts(reg1, reg2) {
                Ok(())
            } else {
                match origin_types(&origin) {
                    None => span_bug!(origin.span(), "bug"),
                    Some(t) => {
                        let (reg1, reg2) = (prepare_display(reg1, ctx), prepare_display(reg2, ctx));
                        let expected = t.expected.fold_with(&mut RegionReplacer{tcx, f: |r| back_map[&r.as_var()]});
                        let expected = prepare_display(expected, ctx);
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
    ctx: CtxRef<'_, 'tcx>,
    def_id: DefId,
    subst: SubstsRef<'tcx>,
) -> (DefId, SubstsRef<'tcx>) {
    match Instance::resolve(ctx.tcx, ctx.param_env(), def_id, subst) {
        Err(_) | Ok(None) => return (def_id, subst), // Can't specialize
        Ok(Some(inst)) => (inst.def.def_id(), inst.substs),
    }
}

struct AllRegionsOutliveCheck<'a, 'tcx> {
    ctx: CtxRef<'a, 'tcx>,
    ts: StateSet,
}

impl<'a, 'tcx> TypeVisitor<TyCtxt<'tcx>> for AllRegionsOutliveCheck<'a, 'tcx> {
    type BreakTy = Region<'tcx>;

    fn visit_ty(&mut self, t: ty::Ty<'tcx>) -> ControlFlow<Self::BreakTy> {
        if self.ctx.static_replacer_info.ty_as_replace_lft_adt(t).is_some() {
            ControlFlow::Continue(()) // these regions mean the wrong thing
        } else {
            t.super_visit_with(self)
        }
    }

    fn visit_region(&mut self, r: Region<'tcx>) -> ControlFlow<Self::BreakTy> {
        if self.ctx.relation.outlived_by(self.ts, r.into()) {
            ControlFlow::Continue(())
        } else {
            ControlFlow::Break(r)
        }
    }
}

fn ty_outlives<'tcx>(
    ty: Ty<'tcx>,
    state: Region<'tcx>,
    ctx: CtxRef<'_, 'tcx>,
) -> Option<Region<'tcx>> {
    ty.ty.visit_with(&mut AllRegionsOutliveCheck { ctx, ts: state.into() }).break_value()
}

pub(crate) fn check_move_state<'tcx>(
    from_state: Region<'tcx>,
    to_state: Region<'tcx>,
    ctx: CtxRef<'_, 'tcx>,
    ty: Ty<'tcx>,
    span: Span,
) -> CreusotResult<Ty<'tcx>> {
    let dty = prepare_display(ty, ctx);
    let d_to_ts = prepare_display(to_state, ctx);
    let d_from_ts = prepare_display(from_state, ctx);
    if to_state == from_state {
        Ok(ty)
    } else if let Some(r) = ty_outlives(ty, to_state, ctx) {
        let r = prepare_display(r, ctx);
        Err(Error::new(span, format!("`{dty}` cannot be moved from `{d_from_ts}` to `{d_to_ts}` since it doesn't live long enough\n`{r}` doesn't outlive `{d_to_ts}`")))
    } else if !ctx.relation.outlives(to_state.into(), from_state.into()) {
        Err(Error::new(
            span,
            format!("`{dty}` cannot be moved from `{d_from_ts}` to `{d_to_ts}` since it didn't exist at that point"),
        ))
    } else {
        let (rty, is_zombie) = ctx.zombie_info.mk_zombie(ty.ty, ctx.tcx, ctx.param_env());
        if is_zombie && !ty.ty.is_mutable_ptr() {
            let e = Error::new(
                span,
                format!("`{dty}` cannot be moved from `{d_from_ts}` to `{d_to_ts}` without becoming a zombie")
            );
            ctx.lint(&PRUSTI_ZOMBIE, span, e.msg())
        }
        Ok(Ty { ty: rty })
    }
}

pub(crate) enum MutDerefType {
    Cur,
    Fin,
}

pub(crate) fn mut_deref<'tcx>(
    ts: Region<'tcx>,
    ctx: CtxRef<'_, 'tcx>,
    ty: Ty<'tcx>,
    span: Span,
) -> CreusotResult<(MutDerefType, Ty<'tcx>)> {
    let (ty, zombie) = match ctx.zombie_info.as_zombie(ty.ty) {
        None => (ty, false),
        Some(ty) => (Ty { ty }, true),
    };
    match ty.as_ref(ts) {
        Some((end, nty, Mutability::Mut)) => match (sub_ts(end, ts), zombie) {
            (true, true) => Ok((Fin, nty)),
            (false, false) => Ok((Cur, nty)),
            (true, false) => {
                ctx.lint(crate::lints::PRUSTI_AMBIGUITY, span, "ambiguous dereference");
                Ok((Cur, nty))
            }
            (false, true) => {
                let end = prepare_display(end, &ctx);
                let ts = prepare_display(ts, &ctx);
                Err(Error::new(span, format!("invalid mut dereference of zombie expression with lifetime `{end}` in state `{ts}`")))
            }
        },
        Some((lft, _, Mutability::Not)) => {
            assert!(!zombie);
            let ty = shr_deref(ts, ctx, ty, span)?;
            let (op, rty) = mut_deref(ts, ctx, ty, span)?;
            Ok((op, Ty::make_ref(lft, rty, ctx.tcx)))
        }
        _ => span_bug!(span, "bug"),
    }
}

pub(crate) fn shr_deref<'tcx>(
    ts: Region<'tcx>,
    ctx: CtxRef<'_, 'tcx>,
    ty: Ty<'tcx>,
    span: Span,
) -> CreusotResult<Ty<'tcx>> {
    let Some((end, nty, Mutability::Not)) = ty.as_ref(ts) else {span_bug!(span, "bug")};
    // if ts has it's home in the current state we should know it's lifetime is longer than it's home
    if ctx.relation.outlived_by(ts.into(), end.into()) {
        Ok(nty)
    } else {
        let end = prepare_display(end, &ctx);
        let ts = prepare_display(ts, &ctx);
        span_bug!(span, "invalid shr reference with lifetime `{end}` existed in state `{ts}`");
    }
}

pub(crate) fn box_deref<'tcx>(
    _ts: Region<'tcx>,
    ctx: CtxRef<'_, 'tcx>,
    ty: Ty<'tcx>,
    span: Span,
) -> CreusotResult<Ty<'tcx>> {
    match ctx.zombie_info.as_zombie(ty.ty) {
        None => Ok(ty.try_unbox().unwrap()),
        Some(_) => Err(Error::new(span, format!("invalid box dereference of zombie expression"))),
    }
}

pub(crate) fn mk_ref<'tcx>(
    _ts: Region<'tcx>,
    lft: Region<'tcx>,
    ctx: CtxRef<'_, 'tcx>,
    ty: Ty<'tcx>,
    _span: Span,
) -> CreusotResult<Ty<'tcx>> {
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
    let interned = InternedInfo::new(tcx);
    let (ctx, ts, arg_tys, (_, expect_res_ty)) =
        full_signature_logic::<Vec<_>>(&interned, trait_home_sig, sig, &ts, impl_id)?;
    let args = arg_tys.into_iter().map(|(_, ty)| Ok((ty, impl_span)));
    let actual_res_ty =
        check_call(&ctx, ts, impl_id, ctx.fix_user_ty_regions(impl_id_subst), args, impl_span)?;
    debug!(
        "{impl_id:?}: expected {}, found {}",
        prepare_display(expect_res_ty, &ctx),
        prepare_display(actual_res_ty, &ctx)
    );
    check_sup(&ctx, expect_res_ty, actual_res_ty, impl_span)
}
