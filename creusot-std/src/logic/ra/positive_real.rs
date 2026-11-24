use crate::{
    logic::{ra::RA, real::PositiveReal},
    prelude::*,
};

impl RA for PositiveReal {
    #[logic(open, inline)]
    fn op(self, other: Self) -> Option<PositiveReal> {
        Some(self + other)
    }

    #[logic(open)]
    fn incl(self, other: Self) -> bool {
        let _ = Self::ext_eq;
        let r = self.to_real() < other.to_real();
        proof_assert!(r ==> self.op(Self::new(other.to_real() - self.to_real())) == Some(other));
        r
    }

    #[logic(open, inline)]
    #[ensures(#[trigger(self == other)] result == (self == other))]
    fn eq(self, other: Self) -> bool {
        self.ext_eq(other)
    }

    #[logic(law)]
    #[allow(unused_variables)]
    fn commutative(a: Self, b: Self) {
        let _ = PositiveReal::ext_eq;
    }

    #[logic]
    fn associative(a: Self, b: Self, c: Self) {
        let _ = PositiveReal::ext_eq;

        let ab = a.op(b).unwrap_logic();
        let bc = b.op(c).unwrap_logic();
        let ab_c = ab.op(c).unwrap_logic();
        let a_bc = a.op(bc).unwrap_logic();
        proof_assert!(ab_c == a_bc)
    }

    #[logic(open, inline)]
    fn core(self) -> Option<Self> {
        None
    }

    #[logic]
    fn core_idemp(self) {}

    #[logic]
    #[allow(unused_variables)]
    fn core_is_maximal_idemp(self, i: Self) {}

    #[logic(open)]
    fn cancelable(self) -> bool {
        let _ = PositiveReal::ext_eq;
        true
    }
}
