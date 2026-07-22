use crate::{
    logic::{int::Positive, ra::RA},
    prelude::*,
};

impl RA for Positive {
    #[logic(open)]
    fn op(self, other: Self) -> Option<Self> {
        Some(self + other)
    }

    #[logic(open)]
    #[ensures(result == (exists<factor> self.op(factor) == Some(other)))]
    fn incl(self, other: Self) -> bool {
        let _ = Self::ext_eq;
        let r = self < other;
        proof_assert!(r ==> self.op(Self::new(other@ - self@)) == Some(other));
        r
    }

    #[logic(law)]
    #[ensures(a.op(b) == b.op(a))]
    fn commutative(a: Self, b: Self) {
        let _ = Self::ext_eq;
    }

    #[logic]
    #[ensures(a.op(b).and_then_logic(|ab: Self| ab.op(c)) == b.op(c).and_then_logic(|bc| a.op(bc)))]
    fn associative(a: Self, b: Self, c: Self) {
        let _ = Self::ext_eq;
    }

    #[logic(open)]
    fn core(self) -> Option<Self> {
        None
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

    #[logic(open)]
    #[ensures(result == (forall<x, y> self.op(x) != None ==>
        self.op(x) == self.op(y) ==> x == y))]
    fn cancelable(self) -> bool {
        let _ = Self::ext_eq;
        true
    }
}
