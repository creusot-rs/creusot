#[cfg(creusot)]
use crate::logic::try_such_that;

use crate::{logic::ra::RA, prelude::*};

/// The 'lattice' Resource Algebra.

pub trait SemiLattice: OrdLogic + Sized {
    #[logic]
    #[ensures(self <= result)]
    #[ensures(other <= result)]
    #[ensures(forall<r> self <= r ==> other <= r ==> result <= r)]
    fn join(self, other: Self) -> Self;
}

impl<T: SemiLattice> RA for T {
    #[logic(open, inline)]
    fn op(self, other: Self) -> Option<Self> {
        Some(self.join(other))
    }

    #[logic]
    #[ensures(match result {
        Some(c) => factor.op(c) == Some(self),
        None => forall<c: Self> factor.op(c) != Some(self),
    })]
    fn factor(self, factor: Self) -> Option<Self> {
        try_such_that(|c| factor.op(c) == Some(self))
    }

    #[logic(law)]
    #[ensures(a.op(b) == b.op(a))]
    fn commutative(a: Self, b: Self) {}

    #[logic]
    #[ensures(a.op(b).and_then_logic(|ab: Self| ab.op(c)) == b.op(c).and_then_logic(|bc| a.op(bc)))]
    fn associative(a: Self, b: Self, c: Self) {}

    #[logic]
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
