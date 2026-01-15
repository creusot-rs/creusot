use crate::{
    logic::{ra::RA, real::PositiveReal},
    prelude::*,
};

impl RA for PositiveReal {
    #[logic(open, inline)]
    fn op(self, other: Self) -> Option<PositiveReal> {
        Some(self + other)
    }

    #[logic(open, inline)]
    #[ensures(match result {
        Some(c) => factor.op(c) == Some(self),
        None => forall<c: Self> factor.op(c) != Some(self),
    })]
    fn factor(self, factor: Self) -> Option<Self> {
        let _ = PositiveReal::ext_eq;
        if self.to_real() > factor.to_real() {
            Some(PositiveReal::new(self.to_real() - factor.to_real()))
        } else {
            None
        }
    }

    #[logic(open, inline)]
    #[ensures(result == (self == other))]
    fn eq(self, other: Self) -> bool {
        self.ext_eq(other)
    }

    #[logic(law)]
    #[ensures(a.op(b) == b.op(a))]
    fn commutative(a: Self, b: Self) {
        let _ = PositiveReal::ext_eq;
    }

    #[logic]
    #[ensures(a.op(b).and_then_logic(|ab: Self| ab.op(c)) == b.op(c).and_then_logic(|bc| a.op(bc)))]
    fn associative(a: Self, b: Self, c: Self) {
        let _ = PositiveReal::ext_eq;
    }

    #[logic(open, inline)]
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
}
