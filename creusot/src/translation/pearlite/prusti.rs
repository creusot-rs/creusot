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
    ty::{self, Binder, FnSig, Region},
};
use rustc_span::{symbol::Symbol, Span};
use smallvec::SmallVec;
use std::{
    hash::Hash,
    ops::{ControlFlow, Deref, DerefMut},
};

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

type Tenv<'tcx> = SemiPersistent<FxHashMap<Symbol, Ty<'tcx>>>;

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

    let (ctx, ts, mut tenv, res_ty) = match home_sig {
        None => {
            let (ctx, ts, arg_tys, res_ty) = full_signature(tcx, sig, ts, owner_id)?;
            let tenv = arg_tys
                .map(|(k, v)| v.map(|v| (k, v)))
                .collect::<CreusotResult<FxHashMap<_, _>>>()?;
            (ctx, ts, tenv, res_ty)
        }
        Some(home_sig) => {
            let (ctx, ts, tenv, res_ty) = full_signature_logic(tcx, home_sig, sig, ts, owner_id)?;
            (ctx, ts, tenv, res_ty)
        }
    };

    if item_id != owner_id.expect_local() {
        tenv.insert(Symbol::intern("result"), res_ty);
    }

    let final_type = convert(&mut term, &mut Tenv::new(tenv), ts, &ctx)?;
    let final_type = strip_derefs_target(&ctx, term.span, ts, final_type, res_ty.ty)?;
    if item_id == owner_id.expect_local() {
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
    let tcx = ctx.tcx;
    match pat {
        Pattern::Constructor { variant, fields, .. } => ty
            .as_adt_variant(*variant, tcx)
            .zip(fields)
            .try_for_each(|(ty, pat)| iterate_bindings(pat, ty, ctx, f)),
        Pattern::Tuple(fields) => ty
            .as_adt_variant(0u32.into(), tcx)
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

// Preforms the conversion and return the type of `term`
// Note: since pearlite doesn't have & and * terms this type may have the wrong number of &'s on the outside
// Recursive calls should generally instead use convert_sdt fix the return type to match the expected type from THIR
// When handling operators that can work over places (currently projection) convert_sdb1
// this leaves behind one layer of reference which is used track the lifetime of the projection
fn convert<'tcx>(
    term: &mut Term<'tcx>,
    tenv: &mut Tenv<'tcx>,
    ts: TimeSlice<'tcx>,
    ctx: &Ctx<'tcx>,
) -> CreusotResult<Ty<'tcx>> {
    let tcx = ctx.tcx;
    let ty = match &mut term.kind {
        TermKind::Var(v) => *tenv.get(v).unwrap(),
        TermKind::Lit(_) | TermKind::Item(_, _) => Ty::with_absurd_home(term.ty, tcx), // Can't return mutable reference
        TermKind::Binary { lhs, rhs, .. } | TermKind::Impl { lhs, rhs } => {
            convert_sdt(&mut *lhs, tenv, ts, ctx)?;
            convert_sdt(&mut *rhs, tenv, ts, ctx)?;
            Ty::with_absurd_home(term.ty, tcx)
        }
        TermKind::Unary { arg, .. } => {
            convert_sdt(&mut *arg, tenv, ts, ctx)?;
            Ty::with_absurd_home(term.ty, tcx)
        }
        TermKind::Forall { binder, body } | TermKind::Exists { binder, body } => {
            let ty = binder.1.tuple_fields()[0];
            let ty = Ty::all_at_ts(ty, ctx.tcx, ts); // TODO handle lifetimes annotations in ty
            convert_sdt(&mut *body, &mut tenv.insert(binder.0, ty), ts, ctx)?
        }
        TermKind::Call { args, fun, id, subst } => {
            let new_reg = if tcx.is_diagnostic_item(Symbol::intern("prusti_curr"), *id) {
                Some(ctx.curr_region())
            } else if tcx.is_diagnostic_item(Symbol::intern("prusti_expiry"), *id) {
                Some(subst.regions().next().unwrap())
            } else if tcx.is_diagnostic_item(Symbol::intern("prusti_dbg_ty"), *id) {
                let mut arg = args.pop().unwrap();
                let res = convert_sdt(&mut arg, tenv, ts, ctx)?;
                eprintln!(
                    "{:?} had type {} (THIR type {})",
                    term.span,
                    prepare_display(res, ctx),
                    term.ty
                );
                term.kind = arg.kind;
                return Ok(res);
            } else {
                None
            };
            if let Some(reg) = new_reg {
                let mut arg = args.pop().unwrap();
                let res = convert_sdt(&mut arg, tenv, reg, &ctx)?;
                term.kind = arg.kind;
                res
            } else {
                let _ = convert_sdt(fun, tenv, ts, ctx)?;
                let args =
                    args.iter_mut().map(|arg| Ok((convert_sdt(arg, tenv, ts, ctx)?, arg.span)));
                let (id, subst) = typeck::try_resolve(&ctx, *id, *subst);
                typeck::check_call(ctx, ts, id, subst, args)?
            }
        }
        TermKind::Constructor { fields, variant, .. } => {
            let fields =
                fields.iter_mut().map(|arg| Ok((convert_sdt(arg, tenv, ts, ctx)?, arg.span)));
            typeck::check_constructor(ctx, fields, term.ty, *variant)?
        }
        TermKind::Tuple { fields, .. } => {
            let fields =
                fields.iter_mut().map(|arg| Ok((convert_sdt(arg, tenv, ts, ctx)?, arg.span)));
            typeck::check_constructor(ctx, fields, term.ty, 0u32.into())?
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
                typeck::shr_deref(ts, ctx, ty, term.span)?;
            }
            let iter = arms.iter_mut().map(|(pat, body)| {
                let iter = PatternIter { pat, ty, ctx };
                convert_sdt(&mut *body, &mut *tenv.insert_many(iter), ts, ctx)
            });
            typeck::union(ctx, term.ty, iter)?
        }
        TermKind::Let { pattern, arg, body } => {
            if matches!(pattern, Pattern::Tuple(..))
                && matches!(&body.kind, TermKind::Var(..))
                && arg.ty == body.ty
            {
                // This was generated by a tuple projection so it should be handled like a projection instead
                let ty = convert_sdb1(&mut *arg, tenv, ts, ctx)?;
                let iter = PatternIter { pat: pattern, ty, ctx };
                convert(&mut *body, &mut *tenv.insert_many(iter), ts, ctx)?
            } else {
                let ty = convert_sdt(&mut *arg, tenv, ts, ctx)?;
                let iter = PatternIter { pat: pattern, ty, ctx };
                convert_sdt(&mut *body, &mut *tenv.insert_many(iter), ts, ctx)?
            }
        }
        TermKind::Projection { lhs, name, .. } => {
            let ty = convert_sdb1(&mut *lhs, tenv, ts, ctx)?;
            let res = ty.as_adt_variant(0u32.into(), tcx).nth(name.as_usize());
            res.unwrap()
        }
        TermKind::Old { term } => convert_sdt(&mut *term, tenv, ctx.old_region(), ctx)?,
        TermKind::Closure { .. } => todo!(),
        TermKind::Absurd => Ty::absurd_regions(term.ty, ctx.tcx),
        _ => return Err(Error::new(term.span, "this operation is not supported in Prusti specs")),
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
