use crate::error::{CreusotResult, Error};

use super::{parsing::Home, region_set::RegionSet};
use rustc_data_structures::fx::FxHashSet;
use rustc_macros::{TyDecodable, TyEncodable, TypeFoldable, TypeVisitable};
use rustc_middle::{
    mir::Mutability,
    ty,
    ty::{
        AdtDef, BoundRegionKind, List, ParamEnv, Region, TyCtxt, TyKind, TypeFoldable, TypeFolder,
    },
};
use rustc_span::{def_id::DefId, Span, Symbol};
use rustc_target::abi::VariantIdx;
use std::{
    fmt::{Debug, Display, Formatter},
    iter,
};
use itertools::Either;

#[derive(Copy, Clone, Debug, TyDecodable, TyEncodable, TypeFoldable, TypeVisitable)]
/// Since we use a different subtyping for this analysis
/// All regions are represented as early bound regions
/// The index is used as a bitset of possible source regions that could have flowed into this region
pub(crate) struct Ty<'tcx> {
    pub(crate) ty: ty::Ty<'tcx>,
    pub(super) home: Region<'tcx>,
}

impl<'tcx> Ty<'tcx> {
    pub(crate) fn as_adt_variant(
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
            TyKind::Tuple(tup) => {
                let tup: &List<ty::Ty> = tup;
                Either::Right(tup.iter())
            }
            _ => unreachable!(),
        };
        tys.zip(iter::repeat(self.home)).map(|(ty, home)| Ty { ty, home })
    }

    pub(crate) fn as_ref(self, ts: Region<'tcx>) -> Option<(Region<'tcx>, Self, Mutability)> {
        match self.ty.kind() {
            &TyKind::Ref(region, ty, m) => Some((region, Ty { ty, home: ts }, m)),
            _ => None,
        }
    }

    pub(crate) fn try_unbox(self) -> Option<Self> {
        match self.ty.kind() {
            &TyKind::Adt(adt, subst) if adt.is_box() => {
                Some(Ty { ty: subst.types().next().unwrap(), home: self.home })
            }
            _ => None,
        }
    }

    pub(crate) fn never(tcx: TyCtxt<'tcx>) -> Self {
        Ty { ty: tcx.types.never, home: RegionSet::EMPTY.into_region(tcx) }
    }

    pub(crate) fn all_at_ts(ty: ty::Ty<'tcx>, tcx: TyCtxt<'tcx>, ts: Region<'tcx>) -> Self {
        Ty { ty: ty.fold_with(&mut RegionReplacer { tcx, f: |_| ts }), home: ts }
    }

    pub(crate) fn absurd_regions(ty: ty::Ty<'tcx>, tcx: TyCtxt<'tcx>) -> Self {
        Self::all_at_ts(ty, tcx,RegionSet::EMPTY.into_region(tcx))
    }

    pub(crate) fn with_absurd_home(ty: ty::Ty<'tcx>, tcx: TyCtxt<'tcx>) -> Self {
        Ty { ty, home: RegionSet::EMPTY.into_region(tcx) }
    }

    pub(crate) fn is_never(self) -> bool {
        self.ty.is_never()
    }

    pub(super) fn has_home_at_ts(self, ts: Region<'tcx>) -> bool {
        sub_ts(self.home, ts)
    }

    pub(super) fn try_new(
        ty: ty::Ty<'tcx>,
        home: Home<Region<'tcx>>,
        span: Span,
    ) -> CreusotResult<Self> {
        let mut ty = ty;
        if home.is_ref {
            if ty.ref_mutability() != Some(Mutability::Not) {
                return Err(Error::new(span, format!("{ty} isn't a shared reference")));
            }
            ty = ty.peel_refs()
        }
        Ok(Ty { ty, home: home.data })
    }
}

pub(super) fn sub_ts<'tcx>(ts1: Region<'tcx>, ts2: Region<'tcx>) -> bool {
    RegionSet::from(ts1).subset(RegionSet::from(ts2))
}

pub(super) struct RegionReplacer<'tcx, F: FnMut(Region<'tcx>) -> Region<'tcx>> {
    pub tcx: TyCtxt<'tcx>,
    pub f: F,
}

impl<'tcx, F: FnMut(Region<'tcx>) -> Region<'tcx>> TypeFolder<TyCtxt<'tcx>>
    for RegionReplacer<'tcx, F>
{
    fn interner(&self) -> TyCtxt<'tcx> {
        self.tcx
    }

    fn fold_region(&mut self, r: Region<'tcx>) -> Region<'tcx> {
        (self.f)(r)
    }
}

const OLD_IDX: u32 = 0;
const CURR_IDX: u32 = 1;
const OLD_REG_SET: RegionSet = RegionSet::singleton(OLD_IDX);
const CURR_REG_SET: RegionSet = RegionSet::singleton(CURR_IDX);

pub(crate) struct Ctx<'tcx> {
    pub tcx: TyCtxt<'tcx>,
    non_blocked: FxHashSet<Region<'tcx>>,
    base_regions: Vec<Region<'tcx>>,
    pub curr_sym: Symbol,
    pub owner_id: DefId,
}

impl<'tcx> Debug for Ctx<'tcx> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Ctx")
            .field("non_blocked", &self.non_blocked)
            .field("base_regions", &self.base_regions)
            .field("owner_id", &self.owner_id)
            .finish_non_exhaustive()
    }
}

fn dummy_region(def_id: DefId, tcx: TyCtxt<'_>, sym: Symbol) -> Region<'_> {
    tcx.mk_re_free(def_id, BoundRegionKind::BrNamed(def_id, sym))
}

impl<'tcx> Ctx<'tcx> {
    pub(crate) fn new(tcx: TyCtxt<'tcx>, owner_id: DefId, is_logic: bool) -> Self {
        let non_blocked = if is_logic {
            iter::empty().collect()
        } else {
            super::variance::empty_regions(tcx, owner_id.expect_local()).collect()
        };
        let curr_sym = Symbol::intern("'curr");
        let curr_region = dummy_region(owner_id, tcx, curr_sym);
        let old_region = dummy_region(owner_id, tcx, Symbol::intern("'old"));
        let base_regions = vec![old_region, curr_region];
        Ctx { tcx, non_blocked, base_regions, curr_sym, owner_id }
    }

    pub(crate) fn old_region(&self) -> Region<'tcx> {
        OLD_REG_SET.into_region(self.tcx)
    }

    pub(crate) fn curr_region(&self) -> Region<'tcx> {
        CURR_REG_SET.into_region(self.tcx)
    }

    pub(super) fn curr_home(&self) -> Home {
        Home{ data: self.curr_sym, is_ref: false }
    }

    /// Checks if a region is legal in a program function
    /// If it's named 'curr it should not be blocked
    pub(super) fn check_ok_in_program(&self, r: Region<'tcx>) -> bool {
        r.get_name() == Some(self.curr_sym) && !self.non_blocked.contains(&r)
    }

    fn region_index_to_name(&self, idx: u32) -> Symbol {
        self.base_regions[idx as usize].get_name().unwrap_or(Symbol::intern("'_"))
    }

    pub(super) fn home_to_region(&mut self, s: Symbol) -> Region<'tcx> {
        for (idx, reg) in self.base_regions.iter().enumerate() {
            if Some(s) == reg.get_name() {
                return RegionSet::singleton(idx as u32).into_region(self.tcx);
            }
        }
        let idx = self.base_regions.len();
        self.base_regions.push(dummy_region(self.owner_id, self.tcx, s));
        RegionSet::singleton(idx as u32).into_region(self.tcx)
    }

    /// Fixes an external region by converting it into a singleton set
    pub(super) fn fix_region(&mut self, r: Region<'tcx>) -> Region<'tcx> {
        if self.non_blocked.contains(&r) || r.get_name() == Some(self.curr_sym) {
            return self.curr_region();
        }
        for (idx, reg) in self.base_regions.iter().enumerate() {
            if r == *reg {
                return RegionSet::singleton(idx as u32).into_region(self.tcx);
            }
        }
        let idx = self.base_regions.len();
        self.base_regions.push(r);
        RegionSet::singleton(idx as u32).into_region(self.tcx)
    }

    pub(super) fn fix_regions<T: TypeFoldable<TyCtxt<'tcx>>>(&mut self, t: T) -> T {
        let tcx = self.tcx;
        t.fold_with(&mut RegionReplacer { tcx, f: |r| self.fix_region(r) })
    }

    pub(super) fn map_parsed_home(&mut self, home: Home) -> Home<Region<'tcx>> {
        Home { data: self.home_to_region(home.data), is_ref: home.is_ref }
    }

    pub(super) fn param_env(&self) -> ParamEnv<'tcx> {
        // We want to ignore outlives constraints
        let base: ParamEnv = self.tcx.param_env(self.owner_id);
        self.tcx.erase_regions(base)
    }
}

pub(super) struct DisplayRegion<'a, 'tcx>(pub Region<'tcx>, pub &'a Ctx<'tcx>);

impl<'a, 'tcx> Display for DisplayRegion<'a, 'tcx> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        let reg_set = RegionSet::from(self.0);
        // write!(f, "({reg_set:?})")?;
        let mut reg_set_h = reg_set;
        match (reg_set_h.next(), reg_set_h.next()) {
            (None, _) => write!(f, "'!"),
            (Some(x), None) => write!(f, "{}", self.1.region_index_to_name(x)),
            _ => {
                write!(f, "{{")?;
                let mut iter = reg_set.map(|x| self.1.region_index_to_name(x));
                write!(f, "{}", iter.next().unwrap())?;
                for x in iter {
                    write!(f, "|{x}")?;
                }
                write!(f, "}}")
            }
        }
    }
}
