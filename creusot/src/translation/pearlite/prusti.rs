use crate::{
    error::{CreusotResult, Error},
    pearlite::{Pattern, Term, TermKind, ThirTerm},
    prusti::{ctx::CtxRef, full_signature, full_signature_logic, typeck, types::*},
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

use crate::{prusti::ctx::InternedInfo, translation::pearlite::BinOp};

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
    let interned = InternedInfo::new(tcx);
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
        None => full_signature(&interned, sig, ts, owner_id)?,
        Some(home_sig) => full_signature_logic(&interned, home_sig, sig, ts, owner_id)?,
    };
    let mut tenv: FxHashMap<_, _> = tenv;

    if item_id != owner_id.expect_local() {
        tenv.insert(Symbol::intern("result"), res_ty);
    }

    let final_type = convert_sdt(&mut term, &mut Tenv::new(tenv), ts, &ctx)?;
    if item_id == owner_id.expect_local() {
        let res_ty = res_ty.1;
        // let final_type = strip_derefs_target(&ctx, term.span, ts, final_type, res_ty.ty)?;
        typeck::check_sup(&ctx, res_ty, final_type, term.span)?
    }
    Ok(term)
}

fn iterate_bindings<'tcx, R, F>(
    pat: &Pattern<'tcx>,
    ty: Ty<'tcx>,
    ctx: CtxRef<'_, 'tcx>,
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
    ctx: CtxRef<'a, 'tcx>,
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
    ctx: CtxRef<'a, 'tcx>,
    ts: Region<'tcx>,
) -> impl InternalIterator<Item = (Symbol, (Region<'tcx>, Ty<'tcx>))> + 'a {
    PatternIter { pat, ty, ctx }.map(move |(k, v)| (k, (ts, v)))
}

fn strip_derefs_target<'tcx>(
    ctx: CtxRef<'_, 'tcx>,
    span: Span,
    current_state: Region<'tcx>,
    (valid_state, ty): (Region<'tcx>, Ty<'tcx>),
    target: ty::Ty<'tcx>,
) -> CreusotResult<(Region<'tcx>, Ty<'tcx>)> {
    let (mut depth, mut target_depth) = (deref_depth(ty.ty, ctx), deref_depth(target, ctx));
    loop {
        if let (Some(x), Some(y)) = (depth.last(), target_depth.last()) && x == y {
            depth.pop();
            target_depth.pop();
        } else {
            break
        }
    }
    let (mut valid_state, mut ty) = (valid_state, ty);
    let mut add_lft = current_state;
    // strip off indirections that aren't in the target type
    if !depth.is_empty() {
        ty = typeck::check_move_state(valid_state, current_state, ctx, ty, span)?;
        valid_state = current_state
    }
    for ind in depth {
        match ind {
            Indirect::Box => {
                ty = typeck::box_deref(current_state, ctx, ty, span)?;
            }
            Indirect::Ref => {
                add_lft = ty.ref_lft();
                ty = typeck::shr_deref(current_state, ctx, ty, span)?;
            }
        }
    }
    for ind in target_depth {
        // add indirections that aren't in current type
        assert!(matches!(ind, Indirect::Ref));
        ty = typeck::mk_ref(current_state, add_lft, ctx, ty, span)?;
        add_lft = current_state;
    }
    // eprintln!("sd {:?} had type {} (THIR type {})", span, prepare_display(ty, ctx), target);
    Ok((valid_state, ty))
}

#[derive(PartialEq, Eq)]
enum Indirect {
    Box,
    Ref,
}

fn deref_depth(ty: ty::Ty<'_>, ctx: CtxRef<'_, '_>) -> SmallVec<[Indirect; 8]> {
    let mut ty = ty;
    let mut res = SmallVec::new();
    loop {
        ty = match ty.kind() {
            ty::TyKind::Ref(_, ty, Not) => {
                res.push(Indirect::Ref);
                *ty
            }
            ty::TyKind::Adt(adt, _) if adt.is_box() => {
                res.push(Indirect::Box);
                ty.boxed_ty()
            }
            _ => match ctx.zombie_info.as_zombie(ty) {
                None => return res,
                Some(ty) => ty,
            },
        };
    }
}

// Preforms the conversion and return the type of `term`
// Note: since pearlite doesn't have & and * terms this type may have the wrong number of &'s on the outside
// Recursive calls should generally instead use convert_sdt fix the return type to match the expected type from THIR
// When handling operators that can work over places (currently projection) convert_sdb1
// this leaves behind one layer of reference which is used track the lifetime of the projection

// Also returns the state the the term is valid in this is usually `ts` but is different for `at` expressions
fn convert<'tcx>(
    outer_term: &mut Term<'tcx>,
    tenv: &mut Tenv<'tcx>,
    ts: TimeSlice<'tcx>,
    ctx: CtxRef<'_, 'tcx>,
) -> CreusotResult<(Region<'tcx>, Ty<'tcx>)> {
    let tcx = ctx.tcx;
    let mut res_state = ts;
    let outer_ty = || ctx.fix_user_ty_regions(outer_term.ty);
    let ty = match &mut outer_term.kind {
        TermKind::Var(v) => {
            let (old_ts, ty) = *tenv.get(v).unwrap();
            typeck::check_move_state(old_ts, ts, ctx, ty, outer_term.span)?
        }
        TermKind::Lit(_) => Ty::with_absurd_home(outer_term.ty, tcx),
        TermKind::Item(id, subst) => {
            let ty = tcx.mk_fn_def(*id, subst.iter().map(|x| ctx.fix_user_ty_regions(x)));
            Ty::with_absurd_home(ty, tcx)
        }
        TermKind::Binary { lhs, rhs, op: BinOp::Eq, .. } => {
            for term in [lhs, rhs] {
                let (_, ty) = convert_sdt_state(&mut *term, tenv, ts, ctx)?;
                if ctx.zombie_info.contains_zombie(ty.ty) {
                    let d_ty = prepare_display(ty, ctx);
                    return Err(Error::new(
                        term.span,
                        format!("binary operation `==` cannot be applied to type `{d_ty}`"),
                    ));
                }
            }
            Ty::with_absurd_home(outer_term.ty, tcx)
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
            let ty = Ty::all_at_ts(ctx.fix_user_ty_regions(ty), ctx.tcx, ts); // TODO handle lifetimes annotations in ty
            convert_sdt(&mut *body, &mut tenv.insert(binder.0, (ts, ty)), ts, ctx)?
        }
        TermKind::Call { args, fun, id, .. } => {
            let ty = convert_sdt(fun, tenv, ts, ctx)?;
            let TyKind::FnDef(_, subst) = ty.ty.kind() else {unreachable!()};
            let new_reg = if tcx.is_diagnostic_item(Symbol::intern("prusti_curr"), *id) {
                Some(ctx.curr_region())
            } else if tcx.is_diagnostic_item(Symbol::intern("prusti_expiry"), *id) {
                let r = subst.regions().next().unwrap();
                ctx.try_move_state(r, fun.span)?;
                Some(r)
            } else if tcx.is_diagnostic_item(Symbol::intern("prusti_dbg_ty"), *id) {
                let mut arg = args.pop().unwrap();
                let res = convert_sdt(&mut arg, tenv, ts, ctx)?;
                let s =
                    format!("had type {} (THIR type {})", prepare_display(res, ctx), outer_term.ty);
                ctx.lint(crate::lints::PRUSTI_DBG_TY, arg.span, s);
                outer_term.kind = arg.kind;
                return Ok((res_state, res));
            } else {
                None
            };
            if let Some(reg) = new_reg {
                let mut arg = args.pop().unwrap();
                let res = convert_sdt(&mut arg, tenv, reg, ctx)?;
                res_state = reg;
                outer_term.kind = arg.kind;
                res
            } else {
                let args = args
                    .iter_mut()
                    .map(|arg| Ok((convert_sdt_state(arg, tenv, ts, ctx)?, arg.span)));
                let (id, subst) = typeck::try_resolve(&ctx, *id, *subst);
                typeck::check_call(ctx, ts, id, subst, args, outer_term.span)?
            }
        }
        TermKind::Constructor { fields, variant, .. } => {
            let fields =
                fields.iter_mut().map(|arg| Ok((convert_sdt(arg, tenv, ts, ctx)?, arg.span)));
            typeck::check_constructor(ctx, fields, outer_ty(), *variant)?
        }
        TermKind::Tuple { fields, .. } => {
            let fields =
                fields.iter_mut().map(|arg| Ok((convert_sdt(arg, tenv, ts, ctx)?, arg.span)));
            typeck::check_constructor(ctx, fields, outer_ty(), 0u32.into())?
        }
        curr @ TermKind::Cur { .. } => {
            let curr_owned = std::mem::replace(curr, TermKind::Absurd);
            let mut term = match curr_owned {
                TermKind::Cur { term } => term,
                _ => unreachable!(),
            };
            let ty = convert_sdb1(&mut term, tenv, ts, ctx)?;
            let (deref_type, inner_ty) = typeck::mut_deref(ts, &ctx, ty, term.span)?;
            *curr = match deref_type {
                typeck::MutDerefType::Cur => TermKind::Cur { term },
                typeck::MutDerefType::Fin => {
                    ctx.lint(crate::lints::PRUSTI_FINAL, term.span, "final operator");
                    TermKind::Fin { term }
                }
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
                let ty = convert_sdt(&mut *body, &mut *tenv.insert_many(iter), ts, ctx)?;
                Ok((ty, body.span))
            });
            typeck::union(ctx, outer_ty(), iter)?
        }
        TermKind::Let { pattern, arg, body } => {
            if matches!(pattern, Pattern::Tuple(..))
                && matches!(&body.kind, TermKind::Var(..))
                && arg.ty == body.ty
            {
                // This was generated by a tuple projection so it should be handled like a projection instead
                let ty = convert_sdb1(&mut *arg, tenv, ts, ctx)?;
                let iter = pattern_iter(pattern, ty, ctx, ts);
                let (rs, ty) = convert(&mut *body, &mut *tenv.insert_many(iter), ts, ctx)?;
                res_state = rs;
                ty
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
            let res = convert_sdt(term, tenv, ctx.old_region(), ctx)?;
            res_state = ctx.old_region();
            res
        }
        TermKind::Closure { .. } => todo!(),
        TermKind::Absurd => Ty::absurd_regions(outer_ty(), ctx.tcx),
        _ => {
            return Err(Error::new(
                outer_term.span,
                "this operation is not supported in Prusti specs",
            ))
        }
    };
    Ok((res_state, ty))
}

fn convert_sdb1<'tcx>(
    term: &mut Term<'tcx>,
    tenv: &mut Tenv<'tcx>,
    ts: TimeSlice<'tcx>,
    ctx: CtxRef<'_, 'tcx>,
) -> CreusotResult<Ty<'tcx>> {
    let sty @ (_, ty) = convert(term, tenv, ts, ctx)?;
    let target = if ty.ty.ref_mutability() == Some(Not) {
        ctx.tcx.mk_imm_ref(ctx.tcx.lifetimes.re_erased, term.ty)
    } else {
        term.ty
    };
    let (valid_state, ty) = strip_derefs_target(ctx, term.span, ts, sty, target)?;
    typeck::check_move_state(valid_state, ts, ctx, ty, term.span)
}

fn convert_sdt<'tcx>(
    term: &mut Term<'tcx>,
    tenv: &mut Tenv<'tcx>,
    ts: TimeSlice<'tcx>,
    ctx: CtxRef<'_, 'tcx>,
) -> CreusotResult<Ty<'tcx>> {
    let (valid_state, ty) = convert_sdt_state(term, tenv, ts, ctx)?;
    typeck::check_move_state(valid_state, ts, ctx, ty, term.span)
}

fn convert_sdt_state<'tcx>(
    term: &mut Term<'tcx>,
    tenv: &mut Tenv<'tcx>,
    ts: TimeSlice<'tcx>,
    ctx: CtxRef<'_, 'tcx>,
) -> CreusotResult<(Region<'tcx>, Ty<'tcx>)> {
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
