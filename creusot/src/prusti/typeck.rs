use super::{
    flat_ty, full_signature_logic,
    parsing::{parse_home_sig_lit, HomeSig},
    region_set::StateSet,
    typeck::MutDerefType::{Cur, Fin},
    types::*,
    util::RegionReplacer,
};
use crate::{
    error::{CreusotResult, Error},
    lints::PRUSTI_ZOMBIE,
    prusti::{
        ctx::{BaseCtx, CtxRef, InternedInfo, STATIC_STATE},
        flat_rust_ty::{flatten_rust_ty, walk_with_rust_flat_ty, RustReg},
        flat_ty::{flatten_ty, CheckSupError},
        parsing::Outlives,
        region_set::State,
        zombie::{pretty_replace, ZombieStatus},
    },
    util,
};
use itertools::Either;
use rustc_ast::Mutability;
use rustc_data_structures::sso::SsoHashMap;
use rustc_index::IndexVec;
use rustc_infer::{infer::TyCtxtInferExt, traits::ObligationCause};
use rustc_middle::{
    bug, span_bug, ty,
    ty::{
        Binder, Instance, InternalSubsts, PolyFnSig, Region, RegionKind, RegionVid, SubstsRef,
        TyCtxt, TyKind, TypeFoldable, TypeVisitable, TypeVisitor,
    },
};
use rustc_span::{def_id::DefId, Span, Symbol};
use rustc_target::abi::VariantIdx;
use rustc_trait_selection::{traits, traits::NormalizeExt};
use std::{iter, ops::ControlFlow};

type SmallVec<T> = smallvec::SmallVec<[T; 4]>;

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

#[derive(Eq, PartialEq, Copy, Clone)]
enum ReVarStatus {
    Bound(StateSet),
    Exact(StateSet),
}

/// Maps region variables to there lower bounds
struct VarInfo(IndexVec<RegionVid, ReVarStatus>);

impl VarInfo {
    fn force_exact(&mut self, idx: RegionVid, exact: StateSet) -> Result<(), CheckSupError> {
        match self.0[idx] {
            ReVarStatus::Bound(expected) if !expected.subset(exact) => {
                return Err(CheckSupError::StateMismatch { expected, found: exact })
            }
            ReVarStatus::Exact(expected) if expected != exact => {
                return Err(CheckSupError::StateMismatch { expected, found: exact })
            }
            _ => {}
        }
        self.0[idx] = ReVarStatus::Exact(exact);
        Ok(())
    }

    fn add_bound(&mut self, expected: RustReg, found: StateSet) -> Result<(), CheckSupError> {
        match expected {
            RustReg::Static => {
                let expected = StateSet::singleton(STATIC_STATE);
                if found.subset(expected) {
                    Ok(())
                } else {
                    Err(CheckSupError::StateMismatch { expected, found })
                }
            }
            RustReg::Var(v) => match self.0[v] {
                ReVarStatus::Bound(ss) => {
                    self.0[v] = ReVarStatus::Bound(ss.union(found));
                    Ok(())
                }
                ReVarStatus::Exact(expected) => {
                    if found.subset(expected) {
                        Ok(())
                    } else {
                        Err(CheckSupError::StateMismatch { expected, found })
                    }
                }
            },
        }
    }

    fn get_region<'tcx>(&self, key: Region<'tcx>, ctx: CtxRef<'_, 'tcx>) -> Region<'tcx> {
        let ss = match key.kind() {
            RegionKind::ReVar(vid) => match self.0[vid] {
                ReVarStatus::Bound(ss) => ss,
                ReVarStatus::Exact(ss) => ss,
            },
            RegionKind::ReStatic => StateSet::singleton(STATIC_STATE),
            _ => bug!(),
        };
        ctx.mk_region(ss)
    }

    fn fold<'tcx>(&self, ty_gen: ty::Ty<'tcx>, ctx: CtxRef<'_, 'tcx>) -> Ty<'tcx> {
        Ty {
            ty: ty_gen
                .fold_with(&mut RegionReplacer { tcx: ctx.tcx, f: |r| self.get_region(r, ctx) }),
        }
    }

    fn get_exact_stateset<'tcx>(&self, vid: RegionVid) -> Option<StateSet> {
        match self.0[vid] {
            ReVarStatus::Bound(_) => None,
            ReVarStatus::Exact(ss) => Some(ss),
        }
    }
}

/// Expand error when expected is a local type
fn expand_error_sup<'tcx>(
    ctx: CtxRef<'_, 'tcx>,
    span: Span,
    expected: Ty<'tcx>,
    found: Ty<'tcx>,
    err: CheckSupError,
) -> Error {
    let expected_raw = display_fold(expected.ty, ctx);
    let found_d = prepare_display(found, ctx);
    match err {
        CheckSupError::ZombieMismatch => {
            Error::new(span, format!("expected `{expected_raw}` found `{found_d}`"))
        }
        CheckSupError::StateMismatch { expected, found } => {
            let expected_r = make_region_for_display(expected, &ctx.base);
            let found_r = make_region_for_display(found, &ctx.base);
            let msg = format!("function was supposed to return data with type `{expected_raw}` but it is returning data with type `{found_d}`\n\
                            expected `{expected_r}` found `{found_r}`");
            Error::new(span, msg)
        }
    }
}

/// Expand error when expected is a generalize rust type
fn expand_error_gen<'tcx>(
    ctx: CtxRef<'_, 'tcx>,
    span: Span,
    var_info: &VarInfo,
    ty_gen: ty::Ty<'tcx>,
    ty: Ty<'tcx>,
    err: CheckSupError,
) -> Error {
    let tcx = ctx.tcx;
    let replacer = |r: Region<'tcx>| match r.kind() {
        RegionKind::ReVar(vid) => match var_info.get_exact_stateset(vid) {
            None => tcx.lifetimes.re_erased,
            Some(ss) => make_region_for_display(ss, ctx),
        },
        RegionKind::ReStatic => tcx.lifetimes.re_static,
        _ => tcx.lifetimes.re_erased,
    };
    let ty_gen = pretty_replace(ctx.interned, replacer, ty_gen);
    let ty = prepare_display(ty, ctx);
    match err {
        CheckSupError::ZombieMismatch => {
            Error::new(span, format!("expected `{ty_gen}` found `{ty}`"))
        }
        CheckSupError::StateMismatch { expected, found } => {
            let expected_r = make_region_for_display(expected, &ctx.base);
            let found_r = make_region_for_display(found, &ctx.base);
            let msg = format!("the expression's lifetime `{found_r}` must match the current time slice `{expected_r}` (found `{ty}`, expected `{ty_gen}`)");
            Error::new(span, msg)
        }
    }
}

fn generalize<'tcx, T: TypeFoldable<TyCtxt<'tcx>>>(tcx: TyCtxt<'tcx>, t: T) -> (T, VarInfo) {
    let mut var_info = IndexVec::new();
    let res = t.fold_with(&mut RegionReplacer {
        tcx,
        f: |_| Region::new_var(tcx, var_info.push(ReVarStatus::Bound(StateSet::EMPTY))),
    });
    (res, VarInfo(var_info))
}

fn check_gen<'tcx>(
    ctx: CtxRef<'_, 'tcx>,
    span: Span,
    ty: Ty<'tcx>,
    ty_gen: ty::Ty<'tcx>,
    var_info: &mut VarInfo,
) -> CreusotResult<()> {
    let flat_gen = flatten_rust_ty(ty_gen);
    let res = walk_with_rust_flat_ty(
        ctx,
        &flat_gen,
        ty,
        |found, expected| var_info.add_bound(expected, found),
        |_, _| span_bug!(span, "bug"),
    );
    res.map_err(|err| expand_error_gen(ctx, span, var_info, ty_gen, ty, err))
}

fn generalize_fn_def<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: DefId,
    var_info: &mut VarInfo,
    subst_ref: SubstsRef<'tcx>,
) -> (ty::Ty<'tcx>, impl Iterator<Item = (Region<'tcx>, Region<'tcx>)>) {
    let fn_ty_gen = tcx.mk_fn_def(def_id, subst_ref);
    let (fn_sig_gen, map) = tcx.replace_late_bound_regions(fn_ty_gen.fn_sig(tcx), |_| {
        Region::new_var(tcx, var_info.0.push(ReVarStatus::Bound(StateSet::EMPTY)))
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

pub(crate) fn check_call<'tcx>(
    ctx: CtxRef<'_, 'tcx>,
    state: State,
    def_id: DefId,
    subst_ref: SubstsRef<'tcx>,
    args: impl Iterator<Item = CreusotResult<((State, Ty<'tcx>), Span)>>,
    call_span: Span,
) -> CreusotResult<Ty<'tcx>> {
    let tcx = ctx.tcx;
    // Eagerly evaluate args to avoid running multiple inference contexts at the same time
    let mut args = args.collect::<CreusotResult<SmallVec<_>>>()?;
    let home_sig = home_sig(ctx, def_id)?;
    let (home_sig_args, home_sig_bounds) = match &home_sig {
        Some(home_sig) => (Either::Left(home_sig.args()), Either::Left(home_sig.bounds())),
        None => (Either::Right(iter::repeat(ctx.curr_home())), Either::Right(iter::empty())),
    };

    let (subst_ref, mut var_info) = generalize(tcx, subst_ref);
    let (fn_ty_gen, iter) = generalize_fn_def(tcx, def_id, &mut var_info, subst_ref);
    let fn_ty_gen = normalize(ctx, fn_ty_gen);
    let subst_iter = filter_elided(iter);

    let (args_gen, res_ty_gen) = match fn_ty_gen.kind() {
        TyKind::FnPtr(bind) => {
            let bind: &PolyFnSig = bind;
            let sig = bind.no_bound_vars().unwrap();
            (sig.inputs(), sig.output())
        }
        _ => span_bug!(call_span, "bug"),
    };

    // maps homes in the home signature to states that were passed in for them
    let mut constrained_homes = SsoHashMap::default();

    for (arg, home_sig_arg) in args.iter_mut().zip(home_sig_args) {
        let ((from_state, ty), span) = arg;
        if home_sig_arg == ctx.curr_sym {
            *ty = check_move_state(*from_state, state, ctx, *ty, *span)?;
        } else {
            match constrained_homes.insert(home_sig_arg, *from_state) {
                Some(oth_state) if oth_state != *from_state => {
                    let d_oth_ts = display_state(oth_state, ctx);
                    let d_this_ts = display_state(*from_state, ctx);
                    return Err(Error::new(*span, format!("expected argument to come from state `{d_oth_ts}`, but it came from `{d_this_ts}`\n\
                    required by home signature of function")));
                }
                _ => {}
            }
        }
    }
    constrained_homes.insert(ctx.curr_sym, state); // 'curr is always constrained to the current state

    // check explicit constraints
    for Outlives { long, short } in home_sig_bounds {
        if let (Some(&long), Some(&short)) =
            (constrained_homes.get(&long), constrained_homes.get(&short))
        {
            if !ctx.relation.outlives_state(StateSet::singleton(long), short) {
                let dlong = display_state(long, ctx);
                let dshort = display_state(short, ctx);
                let msg = format!(
                    "expected `{dlong}` to outlive `{dshort}`\n\
                    required by home signature of function"
                );
                return Err(Error::new(call_span, msg));
            }
        }
    }

    for (home, var) in subst_iter {
        if let Some(&constraint) = constrained_homes.get(&home) {
            var_info.force_exact(var, StateSet::singleton(constraint)).unwrap();
        }
    }

    for (((_, ty), span), ty_gen) in args.into_iter().zip(args_gen) {
        check_gen(ctx, span, ty, *ty_gen, &mut var_info)?;
    }

    let res = var_info.fold(res_ty_gen, ctx);
    if let Some(r) = ty_outlives(res, state, ctx) {
        let dty = prepare_display(res, ctx);
        let dstate = display_state(state, ctx);
        let r = prepare_display(r, ctx);
        let msg = format!("`{dty}` cannot be returned in `{dstate}` since it doesn't live long enough\n`{r}` doesn't outlive `{dstate}`");
        return Err(Error::new(call_span, msg));
    }
    Ok(res)
}

pub(crate) fn check_constructor<'tcx>(
    ctx: CtxRef<'_, 'tcx>,
    fields: impl Iterator<Item = CreusotResult<(Ty<'tcx>, Span)>>,
    target_ty: Ty<'tcx>,
    variant: VariantIdx,
) -> CreusotResult<Ty<'tcx>> {
    let tcx = ctx.tcx;
    // Eagerly evaluate args to avoid running multiple inference contexts at the same time
    let fields = fields.collect::<CreusotResult<SmallVec<_>>>()?.into_iter();

    let (ty_gen, mut var_info) = generalize(tcx, target_ty);
    let fields_gen = ty_gen.as_adt_variant(variant, ctx);

    fields.zip(fields_gen).try_for_each(|((ty, span), Ty { ty: ty_gen })| {
        check_gen(ctx, span, ty, ty_gen, &mut var_info)
    })?;
    Ok(var_info.fold(ty_gen.ty, ctx))
}

pub(crate) fn union<'tcx>(
    ctx: CtxRef<'_, 'tcx>,
    target: ty::Ty<'tcx>,
    elts: impl Iterator<Item = CreusotResult<(Ty<'tcx>, Span)>>,
) -> CreusotResult<Ty<'tcx>> {
    let mut elts = elts.map(|elt| Ok(elt?.0)).collect::<CreusotResult<SmallVec<_>>>()?.into_iter();
    match elts.next() {
        None => Ok(ctx.fix_ty(target, || ctx.interned.mk_region(StateSet::EMPTY))),
        Some(ty) => match elts.next() {
            None => Ok(ty),
            Some(ty2) => {
                let mut flat = flat_ty::flatten_ty(ctx, ty);
                flat_ty::union(ctx, &mut flat, ty2);
                for ty2 in elts {
                    flat_ty::union(ctx, &mut flat, ty2)
                }
                Ok(flat_ty::flat_to_ty(ctx, &flat, ty))
            }
        },
    }
}

pub(super) fn normalize<'tcx, T: TypeFoldable<TyCtxt<'tcx>>>(
    ctx: &'_ BaseCtx<'_, 'tcx>,
    ty: T,
) -> T {
    let tcx = ctx.tcx;
    let infcx = tcx.infer_ctxt().build();
    infcx.at(&ObligationCause::dummy(), ctx.param_env()).normalize(ty).value
}

pub(crate) fn check_sup<'tcx>(
    ctx: CtxRef<'_, 'tcx>,
    expected: Ty<'tcx>,
    actual: Ty<'tcx>,
    span: Span,
) -> CreusotResult<()> {
    let expected_flat = flatten_ty(ctx, expected);
    flat_ty::check_sup(ctx, expected_flat, actual)
        .map_err(|err| expand_error_sup(ctx, span, expected, actual, err))
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
    state: State,
}

impl<'a, 'tcx> TypeVisitor<TyCtxt<'tcx>> for AllRegionsOutliveCheck<'a, 'tcx> {
    type BreakTy = Region<'tcx>;

    fn visit_region(&mut self, r: Region<'tcx>) -> ControlFlow<Self::BreakTy> {
        if self.ctx.relation.outlives_state(r.into(), self.state) {
            ControlFlow::Continue(())
        } else {
            ControlFlow::Break(r)
        }
    }
}

fn ty_outlives<'tcx>(ty: Ty<'tcx>, state: State, ctx: CtxRef<'_, 'tcx>) -> Option<Region<'tcx>> {
    ty.ty.visit_with(&mut AllRegionsOutliveCheck { ctx, state }).break_value()
}

fn is_plain<'tcx>(ctx: CtxRef<'_, 'tcx>, ty: Ty<'tcx>) -> bool {
    let trait_def_id = ctx.plain_def_id;
    let infcx = ctx.tcx.infer_ctxt().build();
    let param_env = ctx.param_env();
    traits::type_known_to_meet_bound_modulo_regions(&infcx, param_env, ty.ty, trait_def_id)
}

pub(crate) fn check_move_state<'tcx>(
    from_state: State,
    to_state: State,
    ctx: CtxRef<'_, 'tcx>,
    ty: Ty<'tcx>,
    span: Span,
) -> CreusotResult<Ty<'tcx>> {
    let dty = prepare_display(ty, ctx);
    let d_to_ts = display_state(to_state, ctx);
    let d_from_ts = display_state(from_state, ctx);
    if to_state == from_state {
        Ok(ty)
    } else if let Some(r) = ty_outlives(ty, to_state, ctx) {
        let r = prepare_display(r, ctx);
        Err(Error::new(span, format!("`{dty}` cannot be moved from `{d_from_ts}` to `{d_to_ts}` since it doesn't live long enough\n`{r}` doesn't outlive `{d_to_ts}`")))
    } else if !(ctx.relation.outlives_state(StateSet::singleton(to_state), from_state)
        || is_plain(ctx, ty))
    {
        Err(Error::new(
            span,
            format!("`{dty}` cannot be moved from `{d_from_ts}` to `{d_to_ts}` since it didn't exist at that point"),
        ))
    } else {
        let (rty, is_zombie) = ty.mk_zombie(ctx);
        if is_zombie && !ty.ty.is_mutable_ptr() {
            let e = Error::new(
                span,
                format!("`{dty}` cannot be moved from `{d_from_ts}` to `{d_to_ts}` without becoming a zombie")
            );
            ctx.lint(&PRUSTI_ZOMBIE, span, e.msg())
        }
        Ok(rty)
    }
}

pub(crate) enum MutDerefType {
    Cur,
    Fin,
}

pub(crate) fn mut_deref<'tcx>(
    state: State,
    ctx: CtxRef<'_, 'tcx>,
    ty: Ty<'tcx>,
    span: Span,
) -> CreusotResult<(MutDerefType, Ty<'tcx>)> {
    match ty.as_ref(ctx) {
        Some((end, nty, zombie, Mutability::Mut)) => {
            match (StateSet::from(end) == StateSet::singleton(state), zombie) {
                (true, ZombieStatus::Zombie) => Ok((Fin, nty)),
                (false, ZombieStatus::NonZombie) => Ok((Cur, nty)),
                (true, ZombieStatus::NonZombie) => {
                    ctx.lint(crate::lints::PRUSTI_AMBIGUITY, span, "ambiguous dereference");
                    Ok((Cur, nty))
                }
                (false, ZombieStatus::Zombie) => {
                    let end = prepare_display(end, &ctx);
                    let state = display_state(state, &ctx);
                    Err(Error::new(span, format!("invalid mut dereference of zombie expression with lifetime `{end}` in state `{state}`")))
                }
            }
        }
        Some((lft, _, _, Mutability::Not)) => {
            let ty = shr_deref(state, ctx, ty, span)?.0;
            let (op, rty) = mut_deref(state, ctx, ty, span)?;
            Ok((op, Ty::make_ref(lft, rty, ctx)))
        }
        _ => span_bug!(span, "bug"),
    }
}

pub(crate) fn shr_deref<'tcx>(
    state: State,
    ctx: CtxRef<'_, 'tcx>,
    ty: Ty<'tcx>,
    span: Span,
) -> CreusotResult<(Ty<'tcx>, Region<'tcx>)> {
    let Some((end, nty, _, Mutability::Not)) = ty.as_ref(ctx) else {span_bug!(span, "bug")};
    // if ts has it's home in the current state we should know it's lifetime is longer than it's home
    if ctx.relation.outlives_state(end.into(), state) {
        Ok((nty, end))
    } else {
        let end = prepare_display(end, &ctx);
        let ts = display_state(state, &ctx);
        span_bug!(span, "invalid shr reference with lifetime `{end}` existed in state `{ts}`");
    }
}

pub(crate) fn box_deref<'tcx>(
    _state: State,
    ctx: CtxRef<'_, 'tcx>,
    ty: Ty<'tcx>,
    span: Span,
) -> CreusotResult<Ty<'tcx>> {
    match ty.unpack(ctx) {
        (ZombieStatus::NonZombie, ty) => match ty.kind() {
            &TyKind::Adt(adt, subst) if adt.is_box() => {
                Ok(Ty { ty: subst.types().next().unwrap() })
            }
            _ => span_bug!(span, "bug"),
        },
        (ZombieStatus::Zombie, _) => {
            Err(Error::new(span, format!("invalid box dereference of zombie expression")))
        }
    }
}

pub(crate) fn mk_ref<'tcx>(
    _state: State,
    lft: Region<'tcx>,
    ctx: CtxRef<'_, 'tcx>,
    ty: Ty<'tcx>,
    _span: Span,
) -> CreusotResult<Ty<'tcx>> {
    Ok(Ty::make_ref(lft, ty, ctx))
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

    let interned = InternedInfo::new(tcx);
    let (ctx, ts, arg_tys, (_, expect_res_ty)) = full_signature_logic::<SmallVec<_>>(
        &interned,
        trait_home_sig,
        Some(refn_subst),
        &ts,
        trait_id,
    )?;
    let args = arg_tys.into_iter().map(|(_, ty)| Ok((ty, impl_span)));
    // lifetimes bound from the impl block that aren't used in the Self type are excluded
    // we can erase these lifetimes since they will disappear after substitution
    let subst_ref = ctx.fix_regions(impl_id_subst, || ctx.tcx.lifetimes.re_erased);
    let actual_res_ty = check_call(&ctx, ts, impl_id, subst_ref, args, impl_span)?;
    debug!(
        "{impl_id:?}: expected {}, found {}",
        prepare_display(expect_res_ty, &ctx),
        prepare_display(actual_res_ty, &ctx)
    );
    check_sup(&ctx, expect_res_ty, actual_res_ty, impl_span)
}
