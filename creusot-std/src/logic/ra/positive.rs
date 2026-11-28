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
    fn incl(self, other: Self) -> bool {
        let _ = Self::ext_eq;
        let r = self < other;
        proof_assert!(r ==> self.op(Self::new(other@ - self@)) == Some(other));
        r
    }

    #[logic(law)]
    #[allow(unused_variables)]
    fn commutative(a: Self, b: Self) {
        let _ = Self::ext_eq;
    }

    #[logic]
    #[allow(unused_variables)]
    fn associative(a: Self, b: Self, c: Self) {
        let _ = Self::ext_eq;
    }

    #[logic(open)]
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
        let _ = Self::ext_eq;
        true
    }
}
