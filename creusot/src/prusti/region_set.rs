use itertools::Itertools;
use rustc_middle::ty::{EarlyBoundRegion, Region, RegionKind, TyCtxt};
use rustc_span::{def_id::CRATE_DEF_ID, symbol::kw};
use std::fmt::{Debug, Formatter};

#[derive(Copy, Clone, PartialEq, Eq)]
pub(crate) struct RegionSet(u32);

impl RegionSet {
    pub const EMPTY: Self = RegionSet(0);
    pub const UNIVERSE: Self = RegionSet(u32::MAX);

    pub const fn singleton(idx: u32) -> Self {
        assert!(idx < u32::BITS);
        RegionSet(1 << idx)
    }

    pub const fn union(self, other: RegionSet) -> RegionSet {
        RegionSet(self.0 | other.0)
    }

    pub const fn intersect(self, other: RegionSet) -> RegionSet {
        RegionSet(self.0 & other.0)
    }

    pub fn subset(self, other: RegionSet) -> bool {
        self.union(other) == other
    }

    pub fn into_region(self, tcx: TyCtxt<'_>) -> Region<'_> {
        let reg =
            EarlyBoundRegion { index: self.0, def_id: CRATE_DEF_ID.to_def_id(), name: kw::In };
        Region::new_early_bound(tcx, reg)
    }

    pub fn try_into_singleton(self) -> Option<u32> {
        let mut iter = self.into_iter();
        let res = iter.next();
        if iter.next().is_none() {
            res
        } else {
            None
        }
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

pub(crate) struct RegionRelation(Box<[RegionSet]>);

/// Invariants self.0.len() is even,
/// self.outlive_sets and self.outlived_by_sets are mirrors,
/// self.outlive_sets is reflexive
impl RegionRelation {
    /// Returns the empty reflexive relation for n regions
    fn with_capacity(n: usize) -> RegionRelation {
        assert!(n <= 32);
        let mut res = RegionRelation(vec![RegionSet::EMPTY; n * 2].into_boxed_slice());
        let n = n as u32;
        (0..n).into_iter().for_each(|i| res.set_outlives(i, i));
        res
    }

    fn size(&self) -> usize {
        self.0.len() / 2
    }

    fn outlive_sets(&self) -> &[RegionSet] {
        &self.0[..self.size()]
    }

    fn outlived_by_sets(&self) -> &[RegionSet] {
        &self.0[self.size()..]
    }

    fn set_outlives(&mut self, r1: u32, r2: u32) {
        let size = self.size();
        let os = &mut self.0[..size][r1 as usize];
        *os = os.union(RegionSet::singleton(r2));
        let obs = &mut self.0[size..][r2 as usize];
        *obs = obs.union(RegionSet::singleton(r1))
    }

    fn square_onto(&self, scratch: &mut RegionRelation) {
        scratch.0.iter_mut().for_each(|x| *x = RegionSet::EMPTY);
        (0..self.size()).into_iter().cartesian_product(0..self.size()).for_each(|(i, j)| {
            if self.outlive_sets()[i].intersect(self.outlived_by_sets()[j]) != RegionSet::EMPTY {
                // There exists a region that i outlives and j is outlived_by so i transitively outlives j
                scratch.set_outlives(i as u32, j as u32)
            }
        })
    }

    /// Note: the relation is always reflexive
    fn transitive_closure(&mut self) {
        let mut scratch = RegionRelation(vec![RegionSet::EMPTY; self.0.len()].into_boxed_slice());
        for _ in 0..self.size().ilog2() + 1 {
            self.square_onto(&mut scratch);
            std::mem::swap(self, &mut scratch);
        }
    }

    pub(super) fn idx_outlives(&self, idx: u32, r2: RegionSet) -> bool {
        match self.outlive_sets().get(idx as usize) {
            Some(s) => r2.subset(*s),
            None => RegionSet::singleton(idx) == r2,
        }
    }

    pub fn idx_outlived_by(&self, idx: u32, r2: RegionSet) -> bool {
        match self.outlived_by_sets().get(idx as usize) {
            Some(s) => r2.subset(*s),
            None => RegionSet::singleton(idx) == r2,
        }
    }

    pub fn outlives(&self, r1: RegionSet, r2: RegionSet) -> bool {
        r1.into_iter().all(|r1| self.idx_outlives(r1, r2))
    }

    /// Returns the same result as self.outlives(r2, r1) but is optimized for r1 being the smaller set
    pub fn outlived_by(&self, r1: RegionSet, r2: RegionSet) -> bool {
        r1.into_iter().all(|r1| self.idx_outlived_by(r1, r2))
    }

    /// Requires all the elements of relation to be less that n
    pub fn new(n: usize, relation: impl Iterator<Item = (u32, u32)>) -> RegionRelation {
        let mut res = Self::with_capacity(n);
        relation.for_each(|(i, j)| res.set_outlives(i, j));
        res.transitive_closure();
        res
    }
}

impl Debug for RegionRelation {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("RegionRelation")
            .field("outlives", &self.outlive_sets())
            .field("outlived_by", &self.outlived_by_sets())
            .finish()
    }
}
