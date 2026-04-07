use crate::{
    logic::{int::Positive, ra::RA},
    prelude::*,
};

impl RA for Positive {
    #[logic(open)]
    fn op(self, other: Self) -> Option<Self> {
        Some(self + other)
    }

    #[logic]
    #[ensures(match result {
        Some(c) => factor.op(c) == Some(self),
        None => forall<c: Self> factor.op(c) != Some(self),
    })]
    fn factor(self, factor: Self) -> Option<Self> {
        if self > factor { Some(Self::new(self.view() - factor.view())) } else { None }
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
