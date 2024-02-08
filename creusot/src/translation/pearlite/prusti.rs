use crate::{
    error::{CreusotResult, Error},
    pearlite::{BinOp, Pattern, Term, TermKind, ThirTerm},
    prusti::{ctx::CtxRef, full_signature, full_signature_logic, typeck, types::*},
    util,
};
use internal_iterator::*;
use rustc_data_structures::sso::SsoHashMap;
use rustc_middle::{
    mir::Mutability::Not,
    span_bug,
    ty::{self, TyKind},
};
use rustc_span::{symbol::Symbol, Span};
use smallvec::SmallVec;
use std::{
    hash::Hash,
    ops::{ControlFlow, Deref, DerefMut},
};

use crate::prusti::{ctx::InternedInfo, FnSigBinder, State};

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
        self.data
    }
}

impl<'a, T, F: FnMut(&mut T)> DerefMut for Revert<'a, T, F> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        self.data
    }
}

impl<'a, T, F: FnMut(&mut T)> Drop for Revert<'a, T, F> {
    fn drop(&mut self) {
        (self.revert)(&mut self.data.0);
    }
}

impl<K: Hash + Eq + Copy, V> SemiPersistent<SsoHashMap<K, V>> {
    fn insert(
        &mut self,
        key: K,
        val: V,
    ) -> Revert<'_, SsoHashMap<K, V>, impl FnMut(&mut SsoHashMap<K, V>)> {
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
    ) -> Revert<'_, SsoHashMap<K, V>, impl FnMut(&mut SsoHashMap<K, V>)> {
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
type Tenv<'tcx> = SemiPersistent<SsoHashMap<Symbol, (State, Ty<'tcx>)>>;

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

    let (ctx, ts, tenv, res_ty) = match home_sig {
        None => full_signature(&interned, ts, owner_id)?,
        Some(home_sig) => {
            full_signature_logic(&interned, home_sig, FnSigBinder::new(tcx, owner_id), ts)?
        }
    };
    let mut tenv: SsoHashMap<_, _> = tenv;

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
    state: State,
) -> impl InternalIterator<Item = (Symbol, (State, Ty<'tcx>))> + 'a {
    PatternIter { pat, ty, ctx }.map(move |(k, v)| (k, (state, v)))
}

fn strip_derefs_target<'tcx>(
    ctx: CtxRef<'_, 'tcx>,
    span: Span,
    current_state: State,
    (valid_state, ty): (State, Ty<'tcx>),
    target: ty::Ty<'tcx>,
) -> CreusotResult<(State, Ty<'tcx>)> {
    let (mut depth, mut target_depth) = (deref_depth_local(ty, ctx), deref_depth_extern(target));
    loop {
        if let (Some(x), Some(y)) = (depth.last(), target_depth.last()) && x == y {
            depth.pop();
            target_depth.pop();
        } else {
            break
        }
    }
    let (mut valid_state, mut ty) = (valid_state, ty);
    let mut add_lft = None;
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
                let r = typeck::shr_deref(current_state, ctx, ty, span)?;
                add_lft = Some(r.1);
                ty = r.0
            }
        }
    }
    for ind in target_depth {
        // add indirections that aren't in current type
        assert!(matches!(ind, Indirect::Ref));
        ty = typeck::mk_ref(
            current_state,
            add_lft.unwrap_or_else(|| ctx.state_to_reg(current_state)),
            ctx,
            ty,
            span,
        )?;
        add_lft = None;
    }
    // eprintln!("sd {:?} had type {} (THIR type {})", span, prepare_display(ty, ctx), target);
    Ok((valid_state, ty))
}

#[derive(PartialEq, Eq)]
enum Indirect {
    Box,
    Ref,
}

fn deref_depth_extern(ty: ty::Ty<'_>) -> SmallVec<[Indirect; 8]> {
    let mut ty = ty;
    let mut res = SmallVec::new();
    loop {
        ty = match ty.kind() {
            TyKind::Ref(_, ty, Not) => {
                res.push(Indirect::Ref);
                *ty
            }
            TyKind::Adt(adt, _) if adt.is_box() => {
                res.push(Indirect::Box);
                ty.boxed_ty()
            }
            _ => return res,
        };
    }
}

fn deref_depth_local<'tcx>(ty: Ty<'tcx>, ctx: CtxRef<'_, 'tcx>) -> SmallVec<[Indirect; 8]> {
    let mut ty = ty;
    let mut res = SmallVec::new();
    loop {
        let unpacked_ty = ty.unpack(ctx).1;
        let inner_ty = match unpacked_ty.kind() {
            TyKind::Ref(_, ty, Not) => {
                res.push(Indirect::Ref);
                *ty
            }
            TyKind::Adt(adt, _) if adt.is_box() => {
                res.push(Indirect::Box);
                unpacked_ty.boxed_ty()
            }
            _ => return res,
        };
        ty = Ty { ty: inner_ty }
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
    state: State,
    ctx: CtxRef<'_, 'tcx>,
) -> CreusotResult<(State, Ty<'tcx>)> {
    let tcx = ctx.tcx;
    let mut res_state = state;
    let ty = match &mut outer_term.kind {
        TermKind::Var(v) => {
            let (old_ts, ty) = *tenv.get(v).unwrap();
            typeck::check_move_state(old_ts, state, ctx, ty, outer_term.span)?
        }
        TermKind::Lit(_) => ctx.fix_ty_with_absurd(outer_term.ty),
        TermKind::Item(id, subst) => {
            let ty = ty::Ty::new_fn_def(ctx.tcx, *id, subst.iter());
            ctx.fix_ty_with_erased(ty)
        }
        TermKind::Binary { lhs, rhs, op: BinOp::Eq | BinOp::Ne, .. } => {
            for term in [lhs, rhs] {
                let (_, ty) = convert_sdt_state(&mut *term, tenv, state, ctx)?;
                if !ty.is_snap_eq(ctx) {
                    let d_ty = prepare_display(ty, ctx);
                    return Err(Error::new(
                        term.span,
                        format!("binary operation `==` cannot be applied to type `{d_ty}` since it doesn't implement `SnapEq`"),
                    ));
                }
            }
            ctx.fix_ty_with_absurd(outer_term.ty)
        }
        TermKind::Binary { lhs, rhs, .. } | TermKind::Impl { lhs, rhs } => {
            convert_sdt(&mut *lhs, tenv, state, ctx)?;
            convert_sdt(&mut *rhs, tenv, state, ctx)?;
            ctx.fix_ty_with_absurd(outer_term.ty)
        }
        TermKind::Unary { arg, .. } => {
            convert_sdt(&mut *arg, tenv, state, ctx)?;
            ctx.fix_ty_with_absurd(outer_term.ty)
        }
        TermKind::Forall { binder, body } | TermKind::Exists { binder, body } => {
            let ty = binder.1.tuple_fields()[0];
            let state_r = ctx.state_to_reg(state);
            let ty = ctx.fix_ty(ty, || state_r); // TODO handle lifetimes annotations in ty
            convert_sdt(&mut *body, &mut tenv.insert(binder.0, (state, ty)), state, ctx)?
        }
        TermKind::Call { args, fun, id, .. } => {
            let ty = convert_sdt(fun, tenv, state, ctx)?;
            let TyKind::FnDef(_, subst) = ty.ty.kind() else { unreachable!() };
            let new_reg = if tcx.is_diagnostic_item(Symbol::intern("prusti_at_post"), *id) {
                Some(ctx.post_state(outer_term.span)?)
            } else if tcx.is_diagnostic_item(Symbol::intern("prusti_at"), *id) {
                let r = subst.regions().next().unwrap();
                let s = ctx.try_move_rstate(r, fun.span)?;
                Some(s)
            } else if tcx.is_diagnostic_item(Symbol::intern("prusti_dbg_ty"), *id) {
                let mut arg = args.pop().unwrap();
                let res = convert_sdt(&mut arg, tenv, state, ctx)?;
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
                    .map(|arg| Ok((convert_sdt_state(arg, tenv, state, ctx)?, arg.span)));
                let (id, subst) = typeck::try_resolve(ctx, *id, subst);
                typeck::check_call(ctx, state, id, subst, args, outer_term.span)?
            }
        }
        TermKind::Constructor { fields, variant, .. } => {
            let fields =
                fields.iter_mut().map(|arg| Ok((convert_sdt(arg, tenv, state, ctx)?, arg.span)));
            let TyKind::Adt(adt, subst) = outer_term.ty.kind() else {
                span_bug!(outer_term.span, "bug")
            };
            typeck::check_constructor(ctx, fields, subst, *adt, *variant, outer_term.span)?
        }
        TermKind::Tuple { fields, .. } => {
            let fields =
                fields.iter_mut().map(|arg| Ok((convert_sdt(arg, tenv, state, ctx)?, arg.span)));
            typeck::check_tuple_constructor(ctx, fields)?
        }
        curr @ TermKind::Cur { .. } => {
            let curr_owned = std::mem::replace(curr, TermKind::Absurd);
            let mut term = match curr_owned {
                TermKind::Cur { term } => term,
                _ => unreachable!(),
            };
            let ty = convert_sdb1(&mut term, tenv, state, ctx)?;
            let (deref_type, inner_ty) = typeck::mut_deref(state, ctx, ty, term.span)?;
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
            let ty = convert_sdt(&mut *scrutinee, tenv, state, ctx)?;
            if ty.ty.is_ref() {
                // We would need to deref the reference to check which variant it has
                typeck::shr_deref(state, ctx, ty, outer_term.span)?;
            }
            let iter = arms.iter_mut().map(|(pat, body)| {
                let iter = pattern_iter(pat, ty, ctx, state);
                let ty = convert_sdt(&mut *body, &mut tenv.insert_many(iter), state, ctx)?;
                Ok((ty, body.span))
            });
            typeck::union(ctx, outer_term.ty, iter)?
        }
        TermKind::Let { pattern, arg, body } => {
            if matches!(pattern, Pattern::Tuple(..))
                && matches!(&body.kind, TermKind::Var(..))
                && arg.ty == body.ty
            {
                // This was generated by a tuple projection so it should be handled like a projection instead
                let ty = convert_sdb1(&mut *arg, tenv, state, ctx)?;
                let iter = pattern_iter(pattern, ty, ctx, state);
                let (rs, ty) = convert(&mut *body, &mut tenv.insert_many(iter), state, ctx)?;
                res_state = rs;
                ty
            } else {
                let ty = convert_sdt(&mut *arg, tenv, state, ctx)?;
                let iter = pattern_iter(pattern, ty, ctx, state);
                convert_sdt(&mut *body, &mut tenv.insert_many(iter), state, ctx)?
            }
        }
        TermKind::Projection { lhs, name, .. } => {
            let ty = convert_sdb1(&mut *lhs, tenv, state, ctx)?;
            let res = ty.as_adt_variant(0u32.into(), ctx).nth(name.as_usize());
            res.unwrap()
        }
        TermKind::Old { term } => {
            let pre_state = ctx.pre_state(outer_term.span)?;
            let res = convert_sdt(term, tenv, pre_state, ctx)?;
            res_state = pre_state;
            res
        }
        TermKind::Closure { .. } => todo!(),
        TermKind::Absurd => ctx.fix_ty_with_absurd(outer_term.ty),
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
    state: State,
    ctx: CtxRef<'_, 'tcx>,
) -> CreusotResult<Ty<'tcx>> {
    let sty @ (_, ty) = convert(term, tenv, state, ctx)?;
    let target = if ty.ty.ref_mutability() == Some(Not) {
        ty::Ty::new_imm_ref(ctx.tcx, ctx.tcx.lifetimes.re_erased, term.ty)
    } else {
        term.ty
    };
    let (valid_state, ty) = strip_derefs_target(ctx, term.span, state, sty, target)?;
    typeck::check_move_state(valid_state, state, ctx, ty, term.span)
}

fn convert_sdt<'tcx>(
    term: &mut Term<'tcx>,
    tenv: &mut Tenv<'tcx>,
    state: State,
    ctx: CtxRef<'_, 'tcx>,
) -> CreusotResult<Ty<'tcx>> {
    let (valid_state, ty) = convert_sdt_state(term, tenv, state, ctx)?;
    typeck::check_move_state(valid_state, state, ctx, ty, term.span)
}

fn convert_sdt_state<'tcx>(
    term: &mut Term<'tcx>,
    tenv: &mut Tenv<'tcx>,
    state: State,
    ctx: CtxRef<'_, 'tcx>,
) -> CreusotResult<(State, Ty<'tcx>)> {
    strip_derefs_target(ctx, term.span, state, convert(term, tenv, state, ctx)?, term.ty)
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
