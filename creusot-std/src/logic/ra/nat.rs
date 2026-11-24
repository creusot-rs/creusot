use crate::{
    logic::{
        Nat,
        ra::{RA, UnitRA},
    },
    prelude::*,
};

impl RA for Nat {
    #[logic(open, inline)]
    fn op(self, other: Self) -> Option<Nat> {
        Some(self + other)
    }

    #[logic(open)]
    fn incl(self, other: Self) -> bool {
        let _ = Self::ext_eq;
        let r = self.to_int() <= other.to_int();
        proof_assert!(r ==> self.op(Self::new(other.to_int() - self.to_int())) == Some(other));
        r
    }

    #[logic(open, inline)]
    #[ensures(#[trigger(self == other)]result == (self == other))]
    fn eq(self, other: Self) -> bool {
        self.ext_eq(other)
    }

    #[logic(law)]
    #[allow(unused_variables)]
    fn commutative(a: Self, b: Self) {
        let _ = Nat::ext_eq;
    }

    #[logic]
    #[allow(unused_variables)]
    fn associative(a: Self, b: Self, c: Self) {
        let _ = Nat::ext_eq;
    }

    #[logic(open, inline)]
    fn core(self) -> Option<Self> {
        Some(Nat::new(0))
    }

    #[logic]
    #[ensures({
        let c = self.core().unwrap_logic();
        c.op(c) == Some(c)
    })]
    #[ensures(self.core().unwrap_logic().op(self) == Some(self))]
    fn core_idemp(self) {
        let _ = Nat::ext_eq;
    }

    #[logic]
    #[allow(unused_variables)]
    fn core_is_maximal_idemp(self, i: Self) {}

    #[logic(open)]
    fn cancelable(self) -> bool {
        let _ = Nat::ext_eq;
        true
    }
}

impl UnitRA for Nat {
    #[logic(open, inline)]
    fn unit() -> Self {
        let _ = Nat::ext_eq;
        Nat::new(0)
    }

    #[logic(open, inline)]
    fn core_total(self) -> Self {
        Nat::new(0)
    }

    #[logic]
    fn core_total_idemp(self) {
        let _ = Nat::ext_eq;
    }
}
