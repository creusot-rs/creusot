use rustc_middle::ty::{EarlyBoundRegion, Region, RegionKind, TyCtxt};
use rustc_span::{def_id::CRATE_DEF_ID, symbol::kw};
use std::fmt::{Debug, Formatter};

#[derive(Copy, Clone, PartialEq, Eq)]
pub(super) struct RegionSet(u32);

impl RegionSet {
    pub const EMPTY: Self = RegionSet(0);

    pub const fn singleton(idx: u32) -> Self {
        assert!(idx < u32::BITS);
        RegionSet(1 << idx)
    }

    pub const fn union(self, other: RegionSet) -> RegionSet {
        RegionSet(self.0 | other.0)
    }

    pub fn subset(self, other: RegionSet) -> bool {
        self.union(other) == other
    }

    pub fn into_region(self, tcx: TyCtxt<'_>) -> Region<'_> {
        let reg =
            EarlyBoundRegion { index: self.0, def_id: CRATE_DEF_ID.to_def_id(), name: kw::Empty };
        tcx.mk_re_early_bound(reg)
    }
}

impl<'tcx> From<Region<'tcx>> for RegionSet {
    fn from(value: Region<'tcx>) -> Self {
        match value.kind() {
            RegionKind::ReEarlyBound(EarlyBoundRegion { index, .. }) => RegionSet(index),
            _ => unreachable!(),
        }
    }
}

impl Iterator for RegionSet {
    type Item = u32;

    fn next(&mut self) -> Option<Self::Item> {
        if *self == RegionSet::EMPTY {
            None
        } else {
            let res = self.0.trailing_zeros();
            self.0 ^= 1 << res;
            Some(res)
        }
    }
}

impl Debug for RegionSet {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "RegionSet({})", self.0)?;
        f.debug_set().entries(*self).finish()
    }
}
