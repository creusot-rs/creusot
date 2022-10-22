use crate::{
    error::{CreusotResult, Error},
    pearlite::{Pattern, Term, TermKind, ThirTerm},
    util,
};
use creusot_rustc::{
    ast::Lit,
    data_structures::fx::{FxHashMap, FxHashSet},
    hir::def_id::DefId,
    middle::{
        mir::Mutability::{Mut, Not},
        ty::{
            self, AdtDef, Binder, BoundRegion, BoundRegionKind, BoundVariableKind, FieldDef, FnSig,
            FreeRegion, GenericParamDefKind, Generics, List, RegionKind, SubstsRef, TyCtxt, TyKind,
        },
    },
    span::{
        def_id::LocalDefId,
        symbol::{Ident, Symbol},
    },
};
use internal_iterator::*;
use itertools::{Either, Itertools};
use std::{
    hash::Hash,
    iter,
    ops::{ControlFlow, Deref, DerefMut},
};
mod parsing;
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

#[derive(Debug, Eq, PartialEq, Copy, Clone, Hash)]
enum Region {
    Named(Symbol),
    Elided(LocalDefId),
    Unknown,
}

impl Region {
    fn new(name: Symbol, d: DefId) -> Region {
        if name.as_str() == "'_" {
            Region::Elided(d.expect_local())
        } else {
            Region::Named(name)
        }
    }
}

impl From<ty::Region<'_>> for Region {
    fn from(region: ty::Region<'_>) -> Self {
        match region.kind() {
            RegionKind::ReEarlyBound(bound) => Region::new(bound.name, bound.def_id),
            RegionKind::ReLateBound(_, BoundRegion { kind: bound, .. })
            | RegionKind::ReFree(FreeRegion { bound_region: bound, .. }) => match bound {
                BoundRegionKind::BrNamed(def_id, name) => Region::new(name, def_id),
                _ => unimplemented!(),
            },
            RegionKind::ReStatic => Region::Named(region.get_name().unwrap()),
            _ => Region::Unknown,
        }
    }
}

#[derive(Copy, Clone, Debug, Eq, PartialEq)]
enum TimeSlice {
    Old,
    Curr,
    Expiry(Region),
}

#[derive(Copy, Clone, Debug)]
enum Lattice<T> {
    Unknown,
    Absurd,
    Inner(T),
}
use Lattice::*;
use TimeSlice::*;

type Home = Lattice<TimeSlice>;

impl<T: Eq> Lattice<T> {
    fn union(self, other: Self) -> Self {
        match (self, other) {
            (Absurd, x) | (x, Absurd) => x,
            (Inner(x), Inner(y)) if x == y => Inner(x),
            _ => Unknown,
        }
    }

    fn matches(self, other: T) -> bool {
        match self {
            Absurd => true,
            Inner(x) => x == other,
            Unknown => false,
        }
    }

    fn subtype(self, other: Self) -> bool {
        match other {
            Absurd => matches!(other, Absurd),
            Inner(y) => self.matches(y),
            Unknown => true,
        }
    }
}

#[derive(Copy, Clone, Debug)]
struct Ty<'tcx> {
    ty: ty::Ty<'tcx>,
    home: Lattice<TimeSlice>,
}

type Tenv<'tcx> = SemiPersistent<FxHashMap<Symbol, Ty<'tcx>>>;

/// Returns region corresponding to `l`
/// Also checks that 'curr is not blocked
fn make_time_slice(
    l: &Lit,
    regions: impl Iterator<Item = Region>,
    non_blocked: &FxHashSet<Region>,
) -> CreusotResult<TimeSlice> {
    let mut bad_curr = false;
    let curr_lifetime = Region::Named(Symbol::intern("'curr"));
    let mut regions = regions
        .inspect(|r| bad_curr = bad_curr || (*r == curr_lifetime && !non_blocked.contains(r)));
    let sym = l.token_lit.symbol;
    let res = match sym.as_str() {
        "old" => Ok(Old),
        "curr" => Ok(Curr),
        "'_" => {
            let mut candiates = (&mut regions)
                .filter(|r| matches!(r, Region::Elided(_)) && !non_blocked.contains(r));
            match (candiates.next(), candiates.next()) {
                (None, _) => Err(Error::new(l.span, "function has no blocked anonymous regions")),
                (Some(_), Some(_)) => {
                    Err(Error::new(l.span, "function has multiple blocked anonymous regions"))
                }
                (Some(c), None) => Ok(Expiry(c)),
            }
        }
        _ => {
            if regions.any(|r| r == Region::Named(sym)) {
                Ok(Expiry(Region::Named(sym)))
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
fn make_time_slice_logic(l: &Lit) -> CreusotResult<TimeSlice> {
    let sym = l.token_lit.symbol;
    match sym.as_str() {
        "old" => Ok(Curr), //hack requires clauses to use same time slice as return
        "curr" => Ok(Curr),
        "'_" => Err(Error::new(
            l.span,
            "expiry contract on logic function must use a concrete lifetime/home",
        )),
        _ => Ok(Expiry(Region::Named(sym))),
    }
}

struct Ctx<'tcx> {
    tcx: TyCtxt<'tcx>,
    non_blocked: FxHashSet<Region>,
}

impl<'tcx> Ctx<'tcx> {
    fn region_to_ts(&self, reg: ty::Region<'tcx>) -> TimeSlice {
        let reg = reg.into();
        if self.non_blocked.contains(&reg) {
            Curr
        } else {
            Expiry(reg)
        }
    }
}

fn make_tenv<'tcx>(
    tcx: TyCtxt<'tcx>,
    owner_id: LocalDefId,
    sig: FnSig<'tcx>,
    home_sig: Option<&Lit>,
) -> CreusotResult<Tenv<'tcx>> {
    let args: &[Ident] = tcx.fn_arg_names(owner_id);
    let (arg_homes, ret_home) = match home_sig {
        Some(lit) => {
            let (arg_homes, ret_home) = parsing::parse_home_sig_lit(lit)?;
            if arg_homes.len() != args.len() {
                return Err(Error::new(lit.span, "number of args doesn't match signature"));
            }
            (Either::Left(arg_homes.into_iter()), ret_home)
        }
        None => {
            let arg_homes = iter::repeat(Inner(Old));
            (Either::Right(arg_homes), Inner(Curr))
        }
    };
    let types = sig.inputs().iter().zip(arg_homes).map(|(&ty, home)| Ty { ty, home });

    let mut tenv: FxHashMap<_, _> = args
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
        .zip(types)
        .collect();
    tenv.insert(Symbol::intern("result"), Ty { ty: sig.output(), home: ret_home });
    Ok(Tenv::new(tenv))
}

pub(super) fn prusti_to_creusot<'tcx>(
    ctx: &ThirTerm<'_, 'tcx>,
    mut term: Term<'tcx>,
) -> CreusotResult<Term<'tcx>> {
    let tcx = ctx.tcx;
    let item_id = ctx.item_id;
    let attr = match util::get_attr_lit(tcx, item_id.to_def_id(), &["creusot", "prusti", "ts"]) {
        None => return Ok(term),
        Some(attr) => attr,
    };

    let owner_id = util::param_def_id(tcx, item_id);
    if tcx.is_closure(owner_id.into()) {
        return Err(Error::new(term.span, "Prusti specs on closures aren't supported"));
    }
    let sig: Binder<FnSig> = tcx.fn_sig(owner_id);
    let bound_vars = sig.bound_vars();
    let generics: &Generics = tcx.generics_of(owner_id);
    let lifetimes1 = bound_vars.iter().filter_map(|x| match x {
        BoundVariableKind::Region(BoundRegionKind::BrNamed(def_id, name)) => {
            Some(Region::new(name, def_id))
        }
        _ => None,
    });
    let lifetimes2 = generics.params.iter().filter_map(|x| match x.kind {
        GenericParamDefKind::Lifetime => {
            let data = x.to_early_bound_region_data();
            Some(Region::new(data.name, data.def_id))
        }
        _ => None,
    });
    let sig = tcx.liberate_late_bound_regions(owner_id.to_def_id(), sig);
    let home_sig = util::get_attr_lit(tcx, owner_id.into(), &["creusot", "prusti", "home_sig"]);
    let non_blocked: FxHashSet<Region> = if home_sig.is_some() {
        iter::once(Region::Named(Symbol::intern("'curr"))).collect()
    } else {
        variance::empty_regions(tcx, owner_id).map(Region::from).collect()
    };
    let ts = if home_sig.is_some() {
        make_time_slice_logic(attr)?
    } else {
        make_time_slice(attr, lifetimes1.chain(lifetimes2), &non_blocked)?
    };
    //dbg!(&non_blocked);
    //eprintln!("{:?}", sig);
    let mut tenv = make_tenv(tcx, owner_id, sig, home_sig)?;
    let ctx = Ctx { tcx, non_blocked };
    let final_type = convert(&mut term, &mut tenv, ts, &ctx)?;
    if item_id == owner_id && !final_type.home.subtype(tenv[&Symbol::intern("result")].home) {
        return Err(Error::new(term.span, "home mismatch"));
    }
    Ok(term)
}

fn iterate_bindings<'tcx, R, F>(
    pat: &Pattern<'tcx>,
    ty: ty::Ty<'tcx>,
    ctx: &Ctx<'tcx>,
    f: &mut F,
) -> ControlFlow<R>
where
    F: FnMut((Symbol, ty::Ty<'tcx>)) -> ControlFlow<R>,
{
    let tcx = ctx.tcx;
    match (ty.kind(), pat) {
        (TyKind::Adt(adt2, subst), Pattern::Constructor { adt, variant, fields, .. }) => {
            debug_assert_eq!(adt, adt2);
            let field_defs = &adt.variants()[*variant].fields;
            field_defs
                .iter()
                .zip(fields)
                .try_for_each(|(def, pat)| iterate_bindings(pat, def.ty(tcx, subst), ctx, f))
        }
        (TyKind::Tuple(tup), Pattern::Tuple(fields)) => {
            let tup: &List<ty::Ty> = tup;
            tup.iter()
                .zip(fields.iter())
                .try_for_each(|(ty, pat)| iterate_bindings(pat, ty, ctx, f))
        }
        (TyKind::Never, Pattern::Constructor { fields, .. } | Pattern::Tuple(fields)) => {
            fields.iter().try_for_each(|pat| iterate_bindings(pat, ty, ctx, f))
        }
        (_, Pattern::Constructor { .. } | Pattern::Tuple(_)) => unreachable!(),
        (_, Pattern::Binder(sym)) => f((*sym, ty)),
        _ => ControlFlow::CONTINUE,
    }
}

struct PatternIter<'a, 'tcx> {
    pat: &'a Pattern<'tcx>,
    ty: ty::Ty<'tcx>,
    ctx: &'a Ctx<'tcx>,
}

impl<'a, 'tcx> InternalIterator for PatternIter<'a, 'tcx> {
    type Item = (Symbol, ty::Ty<'tcx>);

    fn try_for_each<R, F>(self, mut f: F) -> ControlFlow<R>
    where
        F: FnMut(Self::Item) -> ControlFlow<R>,
    {
        iterate_bindings(self.pat, self.ty, self.ctx, &mut f)
    }
}

fn strip_refs(Ty { ty, home }: Ty, ts: TimeSlice) -> Ty {
    match ty.kind() {
        // We must have de-referenced a shared reference,
        // so we'll we set the inner home to the current time slice
        // TODO? if we want to to be strict we could check if this reference is valid at the current time slice
        TyKind::Ref(_, ty, Not) => strip_refs(Ty { ty: *ty, home: Inner(ts) }, ts),
        _ => Ty { ty, home },
    }
}

fn convert<'tcx>(
    term: &mut Term<'tcx>,
    tenv: &mut Tenv<'tcx>,
    ts: TimeSlice,
    ctx: &Ctx<'tcx>,
) -> CreusotResult<Ty<'tcx>> {
    let tcx = ctx.tcx;
    let res = match &mut term.kind {
        TermKind::Var(v) => *tenv.get(v).unwrap(),
        TermKind::Lit(_) | TermKind::Item(_, _) => Ty { ty: term.ty, home: Absurd }, // Can't return mutable reference
        TermKind::Binary { lhs, rhs, .. } => {
            convert(&mut *lhs, tenv, ts, ctx)?;
            convert(&mut *rhs, tenv, ts, ctx)?;
            Ty { ty: term.ty, home: Absurd }
        }
        TermKind::Unary { arg, .. } => {
            convert(&mut *arg, tenv, ts, ctx)?;
            Ty { ty: term.ty, home: Absurd }
        }
        TermKind::Forall { binder, body } | TermKind::Exists { binder, body } => {
            let ty = Ty { ty: binder.1, home: Inner(ts) }; // TODO fix lifetimes in ty
            convert(&mut *body, &mut tenv.insert(binder.0, ty), ts, ctx)?
        }
        TermKind::Call { args, fun, .. } => {
            convert(fun, tenv, ts, ctx)?;
            args.iter_mut().try_for_each(|arg| convert(arg, tenv, ts, ctx).map(drop))?;
            Ty { ty: term.ty, home: Unknown }
        }
        TermKind::Constructor { fields, .. } | TermKind::Tuple { fields } => {
            let home = fields
                .iter_mut()
                .map(|arg| convert(arg, tenv, ts, ctx).map(|x| x.home))
                .fold_ok(Absurd, Lattice::union)?;
            Ty { ty: term.ty, home }
        }
        curr @ TermKind::Cur { .. } => {
            let curr_owned = std::mem::replace(curr, TermKind::Absurd);
            let mut term = match curr_owned {
                TermKind::Cur { term } => term,
                _ => unreachable!(),
            };
            let ty = convert(&mut term, tenv, ts, ctx)?;
            let start = ty.home;
            let (end, ty): (TimeSlice, ty::Ty) = match ty.ty.kind() {
                TyKind::Ref(region, ty, Mut) => (ctx.region_to_ts(*region), *ty),
                TyKind::Never => return Ok(Ty { ty: tcx.mk_ty(TyKind::Never), home: Absurd }),
                _ => unreachable!("curr operator can only apply to mutable references"),
            };
            //eprintln!("start: {start:?}, end: {end:?}");
            let res = match (ts, start, end) {
                (ts, start, _) if start.matches(ts) => TermKind::Cur { term },
                (ts, _, end) if ts == end => TermKind::Fin { term },
                _ => return Err(Error::new(term.span, "Invalid dereference")),
            };
            *curr = res;
            Ty { ty, home: Inner(ts) }
        }
        TermKind::Match { scrutinee, arms } => {
            let Ty { ty, home } = convert(&mut *scrutinee, tenv, ts, ctx)?;
            let home = arms
                .iter_mut()
                .map(|(pat, body)| {
                    let iter = PatternIter { pat, ty, ctx }.map(|(sym, ty)| (sym, Ty { ty, home }));
                    convert(&mut *body, &mut *tenv.insert_many(iter), ts, ctx).map(|x| x.home)
                })
                .fold_ok(Absurd, Lattice::union)?;
            Ty { ty: term.ty, home }
        }
        TermKind::Let { pattern, arg, body } => {
            let Ty { ty, home } = convert(&mut *arg, tenv, ts, ctx)?;
            let iter =
                PatternIter { pat: pattern, ty, ctx }.map(|(sym, ty)| (sym, Ty { ty, home }));
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
        TermKind::Old { term } => convert(&mut *term, tenv, Old, ctx)?,
        TermKind::Closure { .. } => todo!(),
        TermKind::Absurd => Ty { ty: tcx.mk_ty(TyKind::Never), home: Absurd },
        _ => return Err(Error::new(term.span, "The operation is not supported in Prusti specs")),
    };
    Ok(strip_refs(res, ts))
}
