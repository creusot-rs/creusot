use crate::{
    logic::{ord, ra::RA},
    prelude::*,
};

/// The 'lattice' Resource Algebra.
pub struct SemiLattice<T>(pub T);

impl<T: ord::SemiLattice> RA for SemiLattice<T> {
    #[logic(open, inline)]
    fn op(self, other: Self) -> Option<Self> {
        Some(Self(self.0.join(other.0)))
    }

    #[logic(open, inline)]
    fn incl(self, other: Self) -> bool {
        self.0 <= other.0
    }

    #[logic(law)]
    #[allow(unused_variables)]
    fn commutative(a: Self, b: Self) {}

    #[logic]
    #[allow(unused_variables)]
    fn associative(a: Self, b: Self, c: Self) {}

    #[logic(open, inline)]
    fn core(self) -> Option<Self> {
        Some(self)
    }

    #[logic]
    fn core_idemp(self) {}

    #[logic]
    #[allow(unused_variables)]
    fn core_is_maximal_idemp(self, i: Self) {}
}
