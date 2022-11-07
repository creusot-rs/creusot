use crate::{
    error::{CreusotResult, Error},
    pearlite::prusti::parsing::Home,
};
use creusot_rustc::{
    data_structures::fx::{FxHashMap, FxHashSet},
    macros::{TyDecodable, TyEncodable, TypeFoldable, TypeVisitable},
    middle::{
        mir::Mutability,
        ty,
        ty::{
            AdtDef, BoundRegionKind, FreeRegion, List, ParamEnv, Region, RegionKind, TyCtxt,
            TyKind, TypeFoldable, TypeFolder,
        },
    },
    span::{def_id::DefId, Symbol},
    target::abi::VariantIdx,
};
use itertools::Either;
use std::{
    fmt::{Display, Formatter},
    iter,
};
use creusot_rustc::span::Span;

#[derive(Copy, Clone, Debug, TyDecodable, TyEncodable, TypeFoldable, TypeVisitable)]
/// Since we use a different subtyping for this analysis
/// 'static liftimes are represented as ReFree
/// ReStatic is used to represent the global supertype
/// ReErased is used to represent the global subtype
pub(super) struct Ty<'tcx> {
    pub ty: ty::Ty<'tcx>,
    pub home: Region<'tcx>,
}

impl<'tcx> Ty<'tcx> {
    pub(super) fn as_tuple(self) -> impl Iterator<Item = Ty<'tcx>> {
        let tys = match self.ty.kind() {
            TyKind::Tuple(tup) => {
                let tup: &List<ty::Ty> = tup;
                Either::Left(tup.iter())
            }
            TyKind::Never => Either::Right(iter::repeat(self.ty)),
            _ => unreachable!(),
        };
        tys.zip(iter::repeat(self.home)).map(|(ty, home)| Ty { ty, home })
    }

    pub(super) fn as_adt_variant(
        self,
        variant: VariantIdx,
        tcx: TyCtxt<'tcx>,
    ) -> impl Iterator<Item = Ty<'tcx>> {
        let tys = match self.ty.kind() {
            TyKind::Adt(adt, subst_ref) => {
                let adt: AdtDef = *adt;
                let field_defs = &adt.variants()[variant].fields;
                Either::Left(field_defs.iter().map(move |def| def.ty(tcx, *subst_ref)))
            }
            TyKind::Never => Either::Right(iter::repeat(self.ty)),
            _ => unreachable!(),
        };
        tys.zip(iter::repeat(self.home)).map(|(ty, home)| Ty { ty, home })
    }

    pub(super) fn as_ref(self, ts: Region<'tcx>) -> Option<(Region<'tcx>, Self, Mutability)> {
        match self.ty.kind() {
            &TyKind::Ref(region, ty, m) => Some((region, Ty { ty, home: ts }, m)),
            _ => None,
        }
    }

    pub(super) fn try_unbox(self) -> Option<Self> {
        match self.ty.kind() {
            &TyKind::Adt(adt, subst) if adt.is_box() => {
                Some(Ty { ty: subst.types().next().unwrap(), home: self.home })
            }
            _ => None,
        }
    }

    pub(super) fn never(tcx: TyCtxt<'tcx>) -> Self {
        Ty { ty: tcx.types.never, home: tcx.lifetimes.re_static }
    }

    pub(super) fn unknown_regions(ty: ty::Ty<'tcx>, tcx: TyCtxt<'tcx>) -> Self {
        Ty { ty: tcx.erase_regions(ty), home: tcx.lifetimes.re_erased }
    }

    pub(super) fn is_never(self) -> bool {
        self.ty.is_never()
    }

    pub(super) fn has_home_at_ts(self, ts: Region<'tcx>) -> bool {
        sub_ts(self.home, ts)
    }
}

pub(super) fn sub_ts<'tcx>(ts1: Region<'tcx>, ts2: Region<'tcx>) -> bool {
    ts1 == ts2 || ts1.is_static() || ts2.is_erased()
}

pub(super) struct RegionReplacer<'tcx, F: Fn(Region<'tcx>) -> Region<'tcx>> {
    pub tcx: TyCtxt<'tcx>,
    pub f: F,
}

impl<'tcx, F: Fn(Region<'tcx>) -> Region<'tcx>> TypeFolder<'tcx> for RegionReplacer<'tcx, F> {
    fn tcx<'a>(&'a self) -> TyCtxt<'tcx> {
        self.tcx
    }

    fn fold_region(&mut self, r: Region<'tcx>) -> Region<'tcx> {
        (self.f)(r)
    }
}

pub(super) struct Ctx<'tcx> {
    pub tcx: TyCtxt<'tcx>,
    non_blocked: FxHashSet<Region<'tcx>>,
    pub curr_sym: Symbol,
    pub curr_region: Region<'tcx>,
    pub old_region: Region<'tcx>,
    static_region: Region<'tcx>,
    pub owner_id: DefId,
}

fn dummy_region(def_id: DefId, tcx: TyCtxt<'_>, sym: Symbol) -> Region<'_> {
    tcx.mk_region(RegionKind::ReFree(FreeRegion {
        scope: def_id,
        bound_region: BoundRegionKind::BrNamed(def_id, sym),
    }))
}

impl<'tcx> Ctx<'tcx> {
    pub(super) fn new(tcx: TyCtxt<'tcx>, owner_id: DefId, is_logic: bool) -> Self {
        let non_blocked = if is_logic {
            iter::empty().collect()
        } else {
            super::variance::empty_regions(tcx, owner_id.expect_local()).collect()
        };
        let curr_sym = Symbol::intern("'curr");
        let curr_region = dummy_region(owner_id, tcx, curr_sym);
        let old_region = dummy_region(owner_id, tcx, Symbol::intern("old"));
        let static_region = dummy_region(owner_id, tcx, Symbol::intern("'static"));
        Ctx { tcx, non_blocked, curr_sym, curr_region, old_region, static_region, owner_id }
    }

    pub(super) fn absurd_home(&self) -> Region<'tcx> {
        self.tcx.lifetimes.re_static
    }

    /// Checks if a region is legal in a program function
    /// If it's named 'curr it should not be blocked
    pub(super) fn check_ok_in_program(&self, r: Region<'tcx>) -> bool {
        r.get_name() == Some(self.curr_sym) && !self.non_blocked.contains(&r)
    }

    pub(super) fn is_curr(&self, r: Region<'tcx>) -> bool {
        r.get_name() == Some(self.curr_sym) || self.non_blocked.contains(&r)
    }

    /// Fixes an external region by canonizing 'curr
    /// and converting 'static to a ReFree to avoid influencing subtyping rules
    pub(super) fn fix_region(&self, r: Region<'tcx>) -> Region<'tcx> {
        if r.is_static() {
            self.static_region
        } else if r.get_name() == Some(self.old_region.get_name().unwrap()) {
            self.old_region
        } else if self.is_curr(r) {
            self.curr_region
        } else {
            r
        }
    }

    pub(super) fn fix_regions(&self, t: ty::Ty<'tcx>, home: Region<'tcx>) -> Ty<'tcx> {
        let tcx = self.tcx;
        let fixed = t.fold_with(&mut RegionReplacer { tcx, f: |r| self.fix_region(r) });
        Ty { ty: fixed, home }
    }

    pub fn fix_homes(&self, t: ty::Ty<'tcx>, home: Home<Region<'tcx>>, span: Span) -> CreusotResult<Ty<'tcx>> {
        let mut t = t;
        if home.is_ref {
            if t.ref_mutability() != Some(Mutability::Not) {
                return Err(Error::new(
                    span,
                    format!("{t} isn't a shared reference"),
                ));
            }
            t = t.peel_refs()
        }
        Ok(self.fix_regions(t, home.data))
    }

    pub(super) fn parsed_home_to_region(
        &self,
        home: Symbol,
        lifetimes: &FxHashMap<Symbol, Region<'tcx>>,
    ) -> Region<'tcx> {
        lifetimes.get(&home).copied().unwrap_or_else(|| dummy_region(self.owner_id, self.tcx, home))
    }

    pub(super) fn map_parsed_home(
        &self,
        home: Home,
        lifetimes: &FxHashMap<Symbol, Region<'tcx>>,
    ) -> Home<Region<'tcx>> {
        Home { data: self.parsed_home_to_region(home.data, lifetimes), is_ref: home.is_ref }
    }

    pub(super) fn param_env(&self) -> ParamEnv<'tcx> {
        // We want to ignore outlives constraints
        let base: ParamEnv = self.tcx.param_env(self.owner_id);
        self.tcx.erase_regions(base)
    }
}

pub(super) struct DisplayRegion<'tcx>(pub Region<'tcx>);

impl<'tcx> Display for DisplayRegion<'tcx> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self.0.kind() {
            RegionKind::ReStatic => write!(f, "'!"),
            RegionKind::ReErased => write!(f, "'?"),
            _ => write!(f, "{}", self.0),
        }
    }
}
