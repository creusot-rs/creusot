use crate::{
    error::{CreusotResult, Error},
    pearlite::{Pattern, Term, TermKind, ThirTerm},
    util,
};
use creusot_rustc::{
    ast::Lit,
    data_structures::fx::FxHashMap,
    hir::def_id::DefId,
    middle::{
        mir::Mutability::{Mut, Not},
        ty,
        ty::{
            AdtDef, Binder, FieldDef, FnSig, FreeRegion, GenericParamDefKind, Generics, Region,
            RegionKind, SubstsRef, TyKind,
        },
    },
    span::symbol::{Ident, Symbol},
};
use internal_iterator::*;
use itertools::Either;
use std::{
    hash::Hash,
    iter,
    ops::{ControlFlow, Deref, DerefMut},
};

mod parsing;
mod typeck;
pub(crate) use typeck::check_signature_agreement;
mod types;
use types::*;

mod variance;

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
type TimeSlice<'tcx> = Region<'tcx>;

/// Returns region corresponding to `l`
/// Also checks that 'curr is not blocked
fn make_time_slice<'tcx>(
    l: &Lit,
    regions: impl Iterator<Item = Region<'tcx>>,
    ctx: &Ctx<'tcx>,
) -> CreusotResult<TimeSlice<'tcx>> {
    let mut bad_curr = false;
    let mut regions = regions.inspect(|&r| bad_curr = bad_curr || ctx.check_ok_in_program(r));
    let sym = l.token_lit.symbol;
    let res = match sym.as_str() {
        "old" => Ok(ctx.old_region),
        "curr" => Ok(ctx.curr_region),
        "'_" => {
            let mut candiates = (&mut regions).filter(|r| r.get_name() == None && !ctx.is_curr(*r));
            match (candiates.next(), candiates.next()) {
                (None, _) => Err(Error::new(l.span, "function has no blocked anonymous regions")),
                (Some(_), Some(_)) => {
                    Err(Error::new(l.span, "function has multiple blocked anonymous regions"))
                }
                (Some(c), None) => Ok(c),
            }
        }
        _ => {
            if let Some(r) = regions.find(|r| r.get_name() == Some(sym)) {
                Ok(r)
            } else {
                Err(Error::new(l.span, format!("use of undeclared lifetime name {sym}")))
            }
        }
    };
    regions.for_each(drop);
    if bad_curr {
        Err(Error::new(l.span, "'curr region must not be blocked"))
    } else {
        res
    }
}

/// Returns region corresponding to `l` in a logical context
fn make_time_slice_logic<'tcx>(
    l: &Lit,
    map: &FxHashMap<Symbol, Region<'tcx>>,
    ctx: &Ctx<'tcx>,
) -> CreusotResult<TimeSlice<'tcx>> {
    let sym = l.token_lit.symbol;
    match sym.as_str() {
        "old" => Ok(ctx.curr_region), //hack requires clauses to use same time slice as return
        "curr" => Ok(ctx.curr_region),
        "'_" => Err(Error::new(
            l.span,
            "expiry contract on logic function must use a concrete lifetime/home",
        )),
        _ => Ok(ctx.parsed_home_to_region(sym, map)),
    }
}

fn add_homes_to_sig<'a, 'tcx>(
    ctx: &'a Ctx<'tcx>,
    sig: FnSig<'tcx>,
    home_sig: Option<(&Lit, FxHashMap<Symbol, Region<'tcx>>)>,
) -> CreusotResult<(impl Iterator<Item = (Symbol, Ty<'tcx>)> + 'a, Ty<'tcx>)> {
    let args: &[Ident] = ctx.tcx.fn_arg_names(ctx.owner_id);
    let (arg_homes, ret_home) = match home_sig {
        Some((lit, map)) => {
            let (arg_homes, ret_home) = parsing::parse_home_sig_lit(lit)?;
            if arg_homes.len() != args.len() {
                return Err(Error::new(lit.span, "number of args doesn't match signature"));
            }
            let home = ctx.parsed_home_to_region(ret_home, &map);
            (
                Either::Left(
                    arg_homes.into_iter().map(move |h| ctx.parsed_home_to_region(h, &map)),
                ),
                home,
            )
        }
        None => {
            let arg_homes = iter::repeat(ctx.old_region);
            (Either::Right(arg_homes), ctx.curr_region)
        }
    };
    let types = sig.inputs().iter().zip(arg_homes).map(|(&ty, home)| ctx.fix_regions(ty, home));

    let args = args
        .iter()
        .enumerate()
        .map(|(idx, arg)| {
            if arg.name.is_empty() {
                let name = format!("{}", util::AnonymousParamName(idx));
                Symbol::intern(&name)
            } else {
                arg.name
            }
        })
        .zip(types);
    Ok((args, ctx.fix_regions(sig.output(), ret_home)))
}

pub(super) fn prusti_to_creusot<'tcx>(
    ctx: &ThirTerm<'_, 'tcx>,
    mut term: Term<'tcx>,
) -> CreusotResult<Term<'tcx>> {
    let tcx = ctx.tcx;
    let item_id = ctx.item_id;
    let owner_id = util::param_def_id(tcx, item_id).to_def_id();
    if tcx.is_closure(owner_id) {
        return Err(Error::new(term.span, "Prusti specs on closures aren't supported"));
    }

    let home_sig = util::get_attr_lit(tcx, owner_id, &["creusot", "prusti", "home_sig"]);
    let ts = match util::get_attr_lit(tcx, item_id.to_def_id(), &["creusot", "prusti", "ts"]) {
        None => return Ok(term),
        Some(attr) => attr,
    };
    let ctx = Ctx::new(tcx, owner_id, home_sig.is_some());

    let (ts, arg_tys, res_ty) = full_signature(home_sig, ts, owner_id, &ctx)?;
    let res_kv = (Symbol::intern("result"), res_ty);
    let mut tenv = Tenv::new(arg_tys.chain(iter::once(res_kv)).collect());
    let final_type = convert(&mut term, &mut tenv, ts, &ctx)?;
    if item_id == owner_id.expect_local() {
        typeck::check_sup(&ctx, res_ty, final_type, term.span)?
    }
    Ok(term)
}

fn full_signature<'a, 'tcx>(
    home_sig: Option<&Lit>,
    ts: &Lit,
    owner_id: DefId,
    ctx: &'a Ctx<'tcx>,
) -> CreusotResult<(Region<'tcx>, impl Iterator<Item = (Symbol, Ty<'tcx>)> + 'a, Ty<'tcx>)> {
    let tcx = ctx.tcx;
    let sig: Binder<FnSig> = tcx.fn_sig(owner_id);
    let bound_vars = sig.bound_vars();
    let generics: &Generics = tcx.generics_of(owner_id);
    let lifetimes1 = bound_vars.iter().map(|bvk| {
        tcx.mk_region(RegionKind::ReFree(FreeRegion {
            scope: owner_id,
            bound_region: bvk.expect_region(),
        }))
    });
    let lifetimes2 = generics.params.iter().filter_map(|x| match x.kind {
        GenericParamDefKind::Lifetime => {
            let data = x.to_early_bound_region_data();
            Some(tcx.mk_region(RegionKind::ReEarlyBound(data)))
        }
        _ => None,
    });
    let lifetimes = lifetimes1.chain(lifetimes2);

    let sig = tcx.liberate_late_bound_regions(owner_id, sig);

    let (ts, home_sig) = match home_sig {
        Some(lit) => {
            let map: FxHashMap<_, _> =
                lifetimes.filter_map(|r| Some((r.get_name()?, ctx.fix_region(r)))).collect();
            (make_time_slice_logic(ts, &map, &ctx)?, Some((lit, map)))
        }
        None => (make_time_slice(ts, lifetimes, &ctx)?, None),
    };
    let ts = ctx.fix_region(ts);
    //dbg!(&non_blocked);
    //eprintln!("{:?}", sig);
    let (arg_tys, res_ty) = add_homes_to_sig(&ctx, sig, home_sig)?;
    Ok((ts, arg_tys, res_ty))
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
        Pattern::Constructor { adt, variant, fields, .. } => ty
            .as_adt_variant(*adt, *variant, tcx)
            .zip(fields)
            .try_for_each(|(ty, pat)| iterate_bindings(pat, ty, ctx, f)),
        Pattern::Tuple(fields) => {
            ty.as_tuple().zip(fields).try_for_each(|(ty, pat)| iterate_bindings(pat, ty, ctx, f))
        }
        Pattern::Binder(sym) => f((*sym, ty)),
        _ => ControlFlow::CONTINUE,
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

fn ref_depth(ty: ty::Ty<'_>) -> u32 {
    if ty.ref_mutability() == Some(Not) {
        1 + ref_depth(ty.peel_refs())
    } else {
        0
    }
}

fn strip_refs<'tcx>(ty: Ty<'tcx>, ts: TimeSlice<'tcx>, max_depth: u32) -> Ty<'tcx> {
    match ty.as_ref(ts) {
        // We must have de-referenced a shared reference,
        // so we'll we set the inner home to the current time slice
        // TODO? if we want to to be strict we could check if this reference is valid at the current time slice
        Some((_, ty, Not)) if max_depth > 0 => strip_refs(ty, ts, max_depth - 1),
        _ => ty,
    }
}

fn convert<'tcx>(
    term: &mut Term<'tcx>,
    tenv: &mut Tenv<'tcx>,
    ts: TimeSlice<'tcx>,
    ctx: &Ctx<'tcx>,
) -> CreusotResult<Ty<'tcx>> {
    let tcx = ctx.tcx;
    let res = match &mut term.kind {
        TermKind::Var(v) => *tenv.get(v).unwrap(),
        TermKind::Lit(_) | TermKind::Item(_, _) => Ty { ty: term.ty, home: ctx.absurd_home() }, // Can't return mutable reference
        TermKind::Binary { lhs, rhs, .. } => {
            convert(&mut *lhs, tenv, ts, ctx)?;
            convert(&mut *rhs, tenv, ts, ctx)?;
            Ty { ty: term.ty, home: ctx.absurd_home() }
        }
        TermKind::Unary { arg, .. } => {
            convert(&mut *arg, tenv, ts, ctx)?;
            Ty { ty: term.ty, home: ctx.absurd_home() }
        }
        TermKind::Forall { binder, body } | TermKind::Exists { binder, body } => {
            let ty = ctx.fix_regions(binder.1, ts); // TODO handle lifetimes annotations in ty
            convert(&mut *body, &mut tenv.insert(binder.0, ty), ts, ctx)?
        }
        TermKind::Call { args, fun, id, subst } => {
            let _ = convert(fun, tenv, ts, ctx)?;
            let args = args.iter_mut().map(|arg| Ok((convert(arg, tenv, ts, ctx)?, arg.span)));
            let (id, subst) = typeck::try_resolve(&ctx, *id, *subst);
            typeck::check_call(ctx, ts, id, subst, args)?
                .unwrap_or(Ty::unknown_regions(term.ty, tcx))
        }
        TermKind::Constructor { fields, .. } | TermKind::Tuple { fields } => {
            fields.iter_mut().try_for_each(|arg| convert(arg, tenv, ts, ctx).map(drop))?;
            Ty::unknown_regions(term.ty, tcx)
        }
        curr @ TermKind::Cur { .. } => {
            let curr_owned = std::mem::replace(curr, TermKind::Absurd);
            let mut term = match curr_owned {
                TermKind::Cur { term } => term,
                _ => unreachable!(),
            };
            let ty = convert(&mut term, tenv, ts, ctx)?;
            if ty.is_never() {
                return Ok(Ty::never(ctx.tcx));
            }
            let (end, inner_ty, m) = ty.as_ref(ts).unwrap();
            assert!(matches!(m, Mut));
            //eprintln!("start: {start:?}, end: {end:?}");
            let res = match ts {
                ts if ty.has_home_at_ts(ts) => TermKind::Cur { term },
                ts if sub_ts(end, ts) => TermKind::Fin { term },
                _ => return Err(Error::new(term.span, format!("invalid dereference of expression with home `{}` and lifetime `{end}` at time-slice `{ts}`", ty.home))),
            };
            *curr = res;
            inner_ty
        }
        TermKind::Match { scrutinee, arms } => {
            let ty = convert(&mut *scrutinee, tenv, ts, ctx)?;
            let iter = arms.iter_mut().map(|(pat, body)| {
                let iter = PatternIter { pat, ty, ctx };
                convert(&mut *body, &mut *tenv.insert_many(iter), ts, ctx)
            });
            typeck::union(ctx, term.ty, iter)?
        }
        TermKind::Let { pattern, arg, body } => {
            let ty = convert(&mut *arg, tenv, ts, ctx)?;
            let iter = PatternIter { pat: pattern, ty, ctx };
            let x = convert(&mut *body, &mut *tenv.insert_many(iter), ts, ctx)?;
            x
        }
        TermKind::Projection { lhs, name, .. } => {
            let Ty { ty, home } = convert(&mut *lhs, tenv, ts, ctx)?;
            match ty.kind() {
                TyKind::Adt(adt, subst) => {
                    let subst: SubstsRef = subst;
                    let adt: &AdtDef = adt;
                    debug_assert!(adt.is_struct());
                    let def: &FieldDef = &adt.variants()[0u32.into()].fields[name.as_usize()];
                    let ty = def.ty(tcx, subst);
                    Ty { ty, home }
                }
                _ => unreachable!("projection operator can only apply to adts"),
            }
        }
        TermKind::Old { term } => convert(&mut *term, tenv, ctx.old_region, ctx)?,
        TermKind::Closure { .. } => todo!(),
        TermKind::Absurd => Ty::never(ctx.tcx),
        _ => return Err(Error::new(term.span, "The operation is not supported in Prusti specs")),
    };
    let res = strip_refs(res, ts, ref_depth(term.ty));
    Ok(res)
}
