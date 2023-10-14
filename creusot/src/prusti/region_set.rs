use itertools::Itertools;
use rustc_middle::ty::{EarlyBoundRegion, Region, RegionKind, TyCtxt};
use rustc_span::{def_id::CRATE_DEF_ID, symbol::kw};
use std::fmt::{Debug, Formatter};
use rustc_index::Idx;

#[derive(Copy, Clone, PartialEq, Eq, Debug, Hash)]
pub(crate) struct State(pub(super) u32);

impl Idx for State {
    #[inline]
    fn new(idx: usize) -> Self {
        debug_assert!(idx <= u32::MAX as usize);
        State(idx as _)
    }
    #[inline]
    fn index(self) -> usize {
        self.0 as usize
    }
}

impl State {
    pub(super) fn range(n: usize) -> impl Iterator<Item=State> {
        (0..n).map(|i| State::new(i))
    }
}

#[derive(Copy, Clone, PartialEq, Eq)]
pub(crate) struct StateSet(u32);

impl StateSet {
    pub const EMPTY: Self = StateSet(0);
    pub const UNIVERSE: Self = StateSet(u32::MAX);

    pub const fn singleton(state: State) -> Self {
        assert!(state.0 < u32::BITS);
        StateSet(1 << state.0)
    }

    pub const fn union(self, other: StateSet) -> StateSet {
        StateSet(self.0 | other.0)
    }

    pub const fn intersect(self, other: StateSet) -> StateSet {
        StateSet(self.0 & other.0)
    }

    pub fn subset(self, other: StateSet) -> bool {
        self.union(other) == other
    }

    pub fn into_region(self, tcx: TyCtxt<'_>) -> Region<'_> {
        let reg =
            EarlyBoundRegion { index: self.0, def_id: CRATE_DEF_ID.to_def_id(), name: kw::In };
        Region::new_early_bound(tcx, reg)
    }

    pub fn try_into_singleton(self) -> Option<State> {
        let mut iter = self.into_iter();
        let res = iter.next();
        if iter.next().is_none() {
            res
        } else {
            None
        }
    }
}

impl<'tcx> From<Region<'tcx>> for StateSet {
    fn from(value: Region<'tcx>) -> Self {
        match value.kind() {
            RegionKind::ReEarlyBound(EarlyBoundRegion { index, .. }) => StateSet(index),
            _ => unreachable!(),
        }
    }
}

impl Iterator for StateSet {
    type Item = State;

    fn next(&mut self) -> Option<Self::Item> {
        if *self == StateSet::EMPTY {
            None
        } else {
            let res = self.0.trailing_zeros();
            self.0 ^= 1 << res;
            Some(State(res))
        }
    }
}

impl Debug for StateSet {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "RegionSet({})", self.0)?;
        f.debug_set().entries(*self).finish()
    }
}

pub(crate) struct RegionRelation(Box<[StateSet]>);

/// Invariants self.0.len() is even,
/// self.outlive_sets and self.outlived_by_sets are mirrors,
/// self.outlive_sets is reflexive
impl RegionRelation {
    /// Returns the empty reflexive relation for n regions
    fn with_capacity(n: usize) -> RegionRelation {
        assert!(n <= 32);
        let mut res = RegionRelation(vec![StateSet::EMPTY; n * 2].into_boxed_slice());
        (0..n).into_iter().for_each(|i| res.set_outlives(i, i));
        res
    }

    fn size(&self) -> usize {
        self.0.len() / 2
    }

    fn outlive_sets(&self) -> &[StateSet] {
        &self.0[..self.size()]
    }

    fn outlived_by_sets(&self) -> &[StateSet] {
        &self.0[self.size()..]
    }

    fn set_outlives(&mut self, r1: usize, r2: usize) {
        let size = self.size();
        let os = &mut self.0[..size][r1];
        *os = os.union(StateSet::singleton(State(r2 as _)));
        let obs = &mut self.0[size..][r2];
        *obs = obs.union(StateSet::singleton(State(r1 as _)))
    }

    fn square_onto(&self, scratch: &mut RegionRelation) {
        scratch.0.iter_mut().for_each(|x| *x = StateSet::EMPTY);
        (0..self.size()).into_iter().cartesian_product(0..self.size()).for_each(|(i, j)| {
            if self.outlive_sets()[i].intersect(self.outlived_by_sets()[j]) != StateSet::EMPTY {
                // There exists a region that i outlives and j is outlived_by so i transitively outlives j
                scratch.set_outlives(i, j)
            }
        })
    }

    /// Note: the relation is always reflexive
    fn transitive_closure(&mut self) {
        let mut scratch = RegionRelation(vec![StateSet::EMPTY; self.0.len()].into_boxed_slice());
        for _ in 0..self.size().ilog2() + 1 {
            self.square_onto(&mut scratch);
            std::mem::swap(self, &mut scratch);
        }
    }

    pub(super) fn state_outlives(&self, state: State, set: StateSet) -> bool {
        match self.outlive_sets().get(state.index()) {
            Some(s) => set.subset(*s),
            None => StateSet::singleton(state) == set,
        }
    }

    pub fn state_outlived_by(&self, state: State, set: StateSet) -> bool {
        match self.outlived_by_sets().get(state.index()) {
            Some(s) => set.subset(*s),
            None => StateSet::singleton(state) == set,
        }
    }

    pub fn outlives(&self, r1: StateSet, r2: StateSet) -> bool {
        r1.into_iter().all(|r1| self.state_outlives(r1, r2))
    }

    /// Returns the same result as self.outlives(r2, r1) but is optimized for r1 being the smaller set
    pub fn outlived_by(&self, r1: StateSet, r2: StateSet) -> bool {
        r1.into_iter().all(|r1| self.state_outlived_by(r1, r2))
    }

    /// Requires all the elements of relation to be less that n
    pub fn new(n: usize, relation: impl Iterator<Item = (State, State)>) -> RegionRelation {
        let mut res = Self::with_capacity(n);
        relation.for_each(|(i, j)| res.set_outlives(i.index(), j.index()));
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
