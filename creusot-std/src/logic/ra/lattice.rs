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
    #[ensures(result == (exists<factor> self.op(factor) == Some(other)))]
    fn incl(self, other: Self) -> bool {
        self.0 <= other.0
    }

    #[logic(law)]
    #[ensures(a.op(b) == b.op(a))]
    fn commutative(a: Self, b: Self) {}

    #[logic]
    #[ensures(a.op(b).and_then_logic(|ab: Self| ab.op(c)) == b.op(c).and_then_logic(|bc| a.op(bc)))]
    fn associative(a: Self, b: Self, c: Self) {}

    #[logic(open, inline)]
    fn core(self) -> Option<Self> {
        Some(self)
    }

    #[logic]
    #[requires(self.core() != None)]
    #[ensures({
        let c = self.core().unwrap_logic();
        c.op(c) == Some(c)
    })]
    #[ensures(self.core().unwrap_logic().op(self) == Some(self))]
    fn core_idemp(self) {}

    #[logic]
    #[requires(i.op(i) == Some(i))]
    #[requires(i.op(self) == Some(self))]
    #[ensures(match self.core() {
        Some(c) => i.incl(c),
        None => false,
    })]
    fn core_is_maximal_idemp(self, i: Self) {}
}
