use crate::{
    error::{CreusotResult, Error},
    pearlite::{Pattern, Term, TermKind, ThirTerm},
    prusti::{full_signature, full_signature_logic, typeck, types::*},
    util,
};
use internal_iterator::*;
use rustc_data_structures::fx::FxHashMap;
use rustc_middle::{
    mir::Mutability::Not,
    ty::{self, Binder, FnSig, Region, TyKind},
};
use rustc_span::{symbol::Symbol, Span};
use smallvec::SmallVec;
use std::{
    hash::Hash,
    ops::{ControlFlow, Deref, DerefMut},
};

use crate::lints::PRUSTI_ZOMBIE;

type TimeSlice<'tcx> = Region<'tcx>;

#[derive(Debug)]
struct SemiPersistent<T>(T);

impl<T> Deref for SemiPersistent<T> {
    type Target = T;
    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl<T> SemiPersistent<T> {
    fn new(data: T) -> Self {
        SemiPersistent(data)
    }
}

struct Revert<'a, T, F: FnMut(&mut T)> {
    data: &'a mut SemiPersistent<T>,
    revert: F,
}

impl<'a, T, F: FnMut(&mut T)> Deref for Revert<'a, T, F> {
    type Target = SemiPersistent<T>;

    fn deref(&self) -> &Self::Target {
        &self.data
    }
}

impl<'a, T, F: FnMut(&mut T)> DerefMut for Revert<'a, T, F> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.data
    }
}

impl<'a, T, F: FnMut(&mut T)> Drop for Revert<'a, T, F> {
    fn drop(&mut self) {
        (self.revert)(&mut self.data.0);
    }
}

impl<'a, K: Hash + Eq + Copy, V> SemiPersistent<FxHashMap<K, V>> {
    fn insert(
        &mut self,
        key: K,
        val: V,
    ) -> Revert<'_, FxHashMap<K, V>, impl FnMut(&mut FxHashMap<K, V>)> {
        let mut last_val = self.0.insert(key, val);
        Revert {
            data: self,
            revert: move |map| {
                match last_val.take() {
                    None => map.remove(&key),
                    Some(val) => map.insert(key, val),
                };
            },
        }
    }

    fn insert_many(
        &mut self,
        key_vals: impl IntoInternalIterator<Item = (K, V)>,
    ) -> Revert<'_, FxHashMap<K, V>, impl FnMut(&mut FxHashMap<K, V>)> {
        let mut revert_vec: Vec<_> =
            key_vals.into_internal_iter().map(|(k, v)| (k, self.0.insert(k, v))).collect();
        Revert {
            data: self,
            revert: move |map| {
                revert_vec.drain(..).for_each(|(key, last_val)| {
                    match last_val {
                        None => map.remove(&key),
                        Some(val) => map.insert(key, val),
                    };
                });
            },
        }
    }
}

/// Maps identifiers to there type and the time they were bound
type Tenv<'tcx> = SemiPersistent<FxHashMap<Symbol, (TimeSlice<'tcx>, Ty<'tcx>)>>;

pub(super) fn prusti_to_creusot<'tcx>(
    ctx: &ThirTerm<'_, 'tcx>,
    mut term: Term<'tcx>,
) -> CreusotResult<Term<'tcx>> {
    let tcx = ctx.ctx.tcx;
    let item_id = ctx.item_id;
    let owner_id = util::param_def_id(tcx, item_id).to_def_id();

    let ts = match util::get_attr_lit(tcx, item_id.to_def_id(), &["creusot", "prusti", "ts"]) {
        None => return Ok(term),
        Some(attr) => attr,
    };

    if tcx.is_closure(owner_id) {
        return Err(Error::new(term.span, "Prusti specs on closures aren't supported"));
    }

    let home_sig = util::get_attr_lit(tcx, owner_id, &["creusot", "prusti", "home_sig"]);
    let sig: Binder<FnSig> = tcx.fn_sig(owner_id).subst_identity();

    let (ctx, ts, tenv, res_ty) = match home_sig {
        None => full_signature(tcx, sig, ts, owner_id)?,
        Some(home_sig) => full_signature_logic(tcx, home_sig, sig, ts, owner_id)?,
    };
    let mut tenv: FxHashMap<_, _> = tenv;

    if item_id != owner_id.expect_local() {
        tenv.insert(Symbol::intern("result"), res_ty);
    }

    let final_type = convert(&mut term, &mut Tenv::new(tenv), ts, &ctx)?;
    if item_id == owner_id.expect_local() {
        let res_ty = res_ty.1;
        let final_type = strip_derefs_target(&ctx, term.span, ts, final_type, res_ty.ty)?;
        typeck::check_sup(&ctx, res_ty, final_type, term.span)?
    }
    Ok(term)
}

fn iterate_bindings<'tcx, R, F>(
    pat: &Pattern<'tcx>,
    ty: Ty<'tcx>,
    ctx: &Ctx<'tcx>,
    f: &mut F,
) -> ControlFlow<R>
where
    F: FnMut((Symbol, Ty<'tcx>)) -> ControlFlow<R>,
{
    match pat {
        Pattern::Constructor { variant, fields, .. } => ty
            .as_adt_variant(*variant, ctx)
            .zip(fields)
            .try_for_each(|(ty, pat)| iterate_bindings(pat, ty, ctx, f)),
        Pattern::Tuple(fields) => ty
            .as_adt_variant(0u32.into(), ctx)
            .zip(fields)
            .try_for_each(|(ty, pat)| iterate_bindings(pat, ty, ctx, f)),
        Pattern::Binder(sym) => f((*sym, ty)),
        _ => ControlFlow::Continue(()),
    }
}

struct PatternIter<'a, 'tcx> {
    pat: &'a Pattern<'tcx>,
    ty: Ty<'tcx>,
    ctx: &'a Ctx<'tcx>,
}

impl<'a, 'tcx> InternalIterator for PatternIter<'a, 'tcx> {
    type Item = (Symbol, Ty<'tcx>);

    fn try_for_each<R, F>(self, mut f: F) -> ControlFlow<R>
    where
        F: FnMut(Self::Item) -> ControlFlow<R>,
    {
        iterate_bindings(self.pat, self.ty, self.ctx, &mut f)
    }
}

fn pattern_iter<'a, 'tcx>(
    pat: &'a Pattern<'tcx>,
    ty: Ty<'tcx>,
    ctx: &'a Ctx<'tcx>,
    ts: Region<'tcx>,
) -> impl InternalIterator<Item = (Symbol, (Region<'tcx>, Ty<'tcx>))> + 'a {
    PatternIter { pat, ty, ctx }.map(move |(k, v)| (k, (ts, v)))
}

fn strip_derefs_target<'tcx>(
    ctx: &Ctx<'tcx>,
    span: Span,
    ts: TimeSlice<'tcx>,
    ty: Ty<'tcx>,
    target: ty::Ty<'tcx>,
) -> CreusotResult<Ty<'tcx>> {
    let (mut depth, mut target_depth) = (deref_depth(ty.ty), deref_depth(target));
    loop {
        if let (Some(x), Some(y)) = (depth.last(), target_depth.last()) && x == y {
            depth.pop();
            target_depth.pop();
        } else {
            break
        }
    }
    let mut ty = ty;
    let mut add_lft = ts;
    // strip off indirections that aren't in the target type
    for ind in depth {
        match ind {
            Indirect::Box => {
                ty = typeck::box_deref(ts, ctx, ty, span)?;
            }
            Indirect::Ref => {
                add_lft = ty.ref_lft();
                ty = typeck::shr_deref(ts, ctx, ty, span)?;
            }
        }
    }
    for ind in target_depth {
        // add indirections that aren't in current type
        assert!(matches!(ind, Indirect::Ref));
        ty = typeck::mk_ref(ts, add_lft, ctx, ty, span)?;
        add_lft = ts;
    }
    // eprintln!("sd {:?} had type {} (THIR type {})", span, prepare_display(ty, ctx), target);
    Ok(ty)
}

#[derive(PartialEq, Eq)]
enum Indirect {
    Box,
    Ref,
}

fn deref_depth(ty: ty::Ty<'_>) -> SmallVec<[Indirect; 8]> {
    let mut ty = ty;
    let mut res = SmallVec::new();
    loop {
        let (nty, ind) = match ty.kind() {
            ty::TyKind::Ref(_, ty, Not) => (*ty, Indirect::Ref),
            ty::TyKind::Adt(adt, _) if adt.is_box() => (ty.boxed_ty(), Indirect::Box),
            _ => return res,
        };
        ty = nty;
        res.push(ind)
    }
}

fn add_zombie_lint<'tcx>(
    old_ts: Option<Region<'tcx>>,
    ts: Region<'tcx>,
    ctx: &Ctx<'tcx>,
    ty: Ty<'tcx>,
    span: Span,
) -> Ty<'tcx> {
    if ty.ty.is_mutable_ptr() {
        // Add an exception for mutable references
        return ty;
    }
    if let Err(e) = typeck::check_move_ts_with_old(ts, ctx, ty, span, old_ts) {
        let e = e.add_msg(format_args!("\notherwise it would become a zombie"));
        ctx.lint(&PRUSTI_ZOMBIE, span, e.msg())
    }
    ty
}

fn switch_ts<'tcx>(
    term: &mut Term<'tcx>,
    tenv: &mut Tenv<'tcx>,
    old_ts: TimeSlice<'tcx>,
    new_ts: TimeSlice<'tcx>,
    ctx: &Ctx<'tcx>,
    span: Span,
) -> CreusotResult<Ty<'tcx>> {
    let ty = convert_sdt(term, tenv, old_ts, ctx)?;
    Ok(add_zombie_lint(Some(old_ts), new_ts, ctx, ty, span))
}

// Preforms the conversion and return the type of `term`
// Note: since pearlite doesn't have & and * terms this type may have the wrong number of &'s on the outside
// Recursive calls should generally instead use convert_sdt fix the return type to match the expected type from THIR
// When handling operators that can work over places (currently projection) convert_sdb1
// this leaves behind one layer of reference which is used track the lifetime of the projection
fn convert<'tcx>(
    outer_term: &mut Term<'tcx>,
    tenv: &mut Tenv<'tcx>,
    ts: TimeSlice<'tcx>,
    ctx: &Ctx<'tcx>,
) -> CreusotResult<Ty<'tcx>> {
    let tcx = ctx.tcx;
    let ty = match &mut outer_term.kind {
        TermKind::Var(v) => {
            let (old_ts, ty) = *tenv.get(v).unwrap();
            add_zombie_lint(Some(old_ts), ts, ctx, ty, outer_term.span)
        }
        TermKind::Lit(_) => Ty::with_absurd_home(outer_term.ty, tcx),
        TermKind::Item(id, subst) => {
            let ty = tcx.mk_fn_def(*id, subst.iter().map(|x| ctx.fix_user_ty_regions(x)));
            Ty::with_absurd_home(ty, tcx)
        }
        TermKind::Binary { lhs, rhs, .. } | TermKind::Impl { lhs, rhs } => {
            convert_sdt(&mut *lhs, tenv, ts, ctx)?;
            convert_sdt(&mut *rhs, tenv, ts, ctx)?;
            Ty::with_absurd_home(outer_term.ty, tcx)
        }
        TermKind::Unary { arg, .. } => {
            convert_sdt(&mut *arg, tenv, ts, ctx)?;
            Ty::with_absurd_home(outer_term.ty, tcx)
        }
        TermKind::Forall { binder, body } | TermKind::Exists { binder, body } => {
            let ty = binder.1.tuple_fields()[0];
            let ty = Ty::all_at_ts(ty, ctx.tcx, ts); // TODO handle lifetimes annotations in ty
            convert_sdt(&mut *body, &mut tenv.insert(binder.0, (ts, ty)), ts, ctx)?
        }
        TermKind::Call { args, fun, id, .. } => {
            let ty = convert_sdt(fun, tenv, ts, ctx)?;
            let TyKind::FnDef(_, subst) = ty.ty.kind() else {unreachable!()};
            let new_reg = if tcx.is_diagnostic_item(Symbol::intern("prusti_curr"), *id) {
                Some(ctx.curr_region())
            } else if tcx.is_diagnostic_item(Symbol::intern("prusti_expiry"), *id) {
                let r = subst.regions().next().unwrap();
                if r == ctx.tcx.lifetimes.re_erased {
                    return Err(Error::new(fun.span, "at_expiry must be given an explicit region"));
                } else {
                    Some(r)
                }
            } else if tcx.is_diagnostic_item(Symbol::intern("prusti_dbg_ty"), *id) {
                let mut arg = args.pop().unwrap();
                let res = convert_sdt(&mut arg, tenv, ts, ctx)?;
                eprintln!(
                    "{:?} had type {} (THIR type {})",
                    outer_term.span,
                    prepare_display(res, ctx),
                    outer_term.ty
                );
                outer_term.kind = arg.kind;
                return Ok(res);
            } else {
                None
            };
            if let Some(reg) = new_reg {
                let mut arg = args.pop().unwrap();
                let res = switch_ts(&mut arg, tenv, reg, ts, ctx, outer_term.span)?;
                outer_term.kind = arg.kind;
                res
            } else {
                let args =
                    args.iter_mut().map(|arg| Ok((convert_sdt(arg, tenv, ts, ctx)?, arg.span)));
                let (id, subst) = typeck::try_resolve(&ctx, *id, *subst);
                let ty = typeck::check_call(ctx, ts, id, subst, args)?;
                add_zombie_lint(None, ts, ctx, ty, outer_term.span)
            }
        }
        TermKind::Constructor { fields, variant, .. } => {
            let fields =
                fields.iter_mut().map(|arg| Ok((convert_sdt(arg, tenv, ts, ctx)?, arg.span)));
            typeck::check_constructor(ctx, fields, outer_term.ty, *variant)?
        }
        TermKind::Tuple { fields, .. } => {
            let fields =
                fields.iter_mut().map(|arg| Ok((convert_sdt(arg, tenv, ts, ctx)?, arg.span)));
            typeck::check_constructor(ctx, fields, outer_term.ty, 0u32.into())?
        }
        curr @ TermKind::Cur { .. } => {
            let curr_owned = std::mem::replace(curr, TermKind::Absurd);
            let mut term = match curr_owned {
                TermKind::Cur { term } => term,
                _ => unreachable!(),
            };
            let ty = convert_sdt(&mut term, tenv, ts, ctx)?;
            if ty.is_never() {
                return Ok(Ty::never(ctx.tcx));
            }
            let (deref_type, inner_ty) = typeck::mut_deref(ts, &ctx, ty, term.span)?;
            *curr = match deref_type {
                typeck::MutDerefType::Cur => TermKind::Cur { term },
                typeck::MutDerefType::Fin => TermKind::Fin { term },
            };
            inner_ty
        }
        TermKind::Match { scrutinee, arms } => {
            let ty = convert_sdt(&mut *scrutinee, tenv, ts, ctx)?;
            if ty.ty.is_ref() {
                // We would need to deref the reference to check which variant it has
                typeck::shr_deref(ts, ctx, ty, outer_term.span)?;
            }
            let iter = arms.iter_mut().map(|(pat, body)| {
                let iter = pattern_iter(pat, ty, ctx, ts);
                convert_sdt(&mut *body, &mut *tenv.insert_many(iter), ts, ctx)
            });
            typeck::union(ctx, outer_term.ty, iter)?
        }
        TermKind::Let { pattern, arg, body } => {
            if matches!(pattern, Pattern::Tuple(..))
                && matches!(&body.kind, TermKind::Var(..))
                && arg.ty == body.ty
            {
                // This was generated by a tuple projection so it should be handled like a projection instead
                let ty = convert_sdb1(&mut *arg, tenv, ts, ctx)?;
                let iter = pattern_iter(pattern, ty, ctx, ts);
                convert(&mut *body, &mut *tenv.insert_many(iter), ts, ctx)?
            } else {
                let ty = convert_sdt(&mut *arg, tenv, ts, ctx)?;
                let iter = pattern_iter(pattern, ty, ctx, ts);
                convert_sdt(&mut *body, &mut *tenv.insert_many(iter), ts, ctx)?
            }
        }
        TermKind::Projection { lhs, name, .. } => {
            let ty = convert_sdb1(&mut *lhs, tenv, ts, ctx)?;
            let res = ty.as_adt_variant(0u32.into(), ctx).nth(name.as_usize());
            res.unwrap()
        }
        TermKind::Old { term } => {
            switch_ts(term, tenv, ctx.old_region(), ts, ctx, outer_term.span)?
        }
        TermKind::Closure { .. } => todo!(),
        TermKind::Absurd => Ty::absurd_regions(outer_term.ty, ctx.tcx),
        _ => {
            return Err(Error::new(
                outer_term.span,
                "this operation is not supported in Prusti specs",
            ))
        }
    };
    Ok(ty)
}

fn convert_sdb1<'tcx>(
    term: &mut Term<'tcx>,
    tenv: &mut Tenv<'tcx>,
    ts: TimeSlice<'tcx>,
    ctx: &Ctx<'tcx>,
) -> CreusotResult<Ty<'tcx>> {
    let ty = convert(term, tenv, ts, ctx)?;
    let target = if ty.ty.ref_mutability() == Some(Not) {
        ctx.tcx.mk_imm_ref(ctx.tcx.lifetimes.re_erased, term.ty)
    } else {
        term.ty
    };
    strip_derefs_target(ctx, term.span, ts, ty, target)
}

fn convert_sdt<'tcx>(
    term: &mut Term<'tcx>,
    tenv: &mut Tenv<'tcx>,
    ts: TimeSlice<'tcx>,
    ctx: &Ctx<'tcx>,
) -> CreusotResult<Ty<'tcx>> {
    strip_derefs_target(ctx, term.span, ts, convert(term, tenv, ts, ctx)?, term.ty)
}

impl<'tcx> Term<'tcx> {}

pub(crate) fn strip_all_refs(ty: ty::Ty) -> ty::Ty {
    let mut ty = ty;
    loop {
        if ty.ref_mutability() == Some(Not) || ty.is_box() {
            ty = ty.builtin_deref(true).unwrap().ty;
        } else {
            return ty;
        }
    }
}
