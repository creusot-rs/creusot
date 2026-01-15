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

    #[logic(open, inline)]
    #[ensures(match result {
        Some(c) => factor.op(c) == Some(self),
        None => forall<c: Self> factor.op(c) != Some(self),
    })]
    fn factor(self, factor: Self) -> Option<Self> {
        let _ = Nat::ext_eq;
        if self.to_int() >= factor.to_int() {
            Some(Nat::new(self.to_int() - factor.to_int()))
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
        let _ = Nat::ext_eq;
    }

    #[logic]
    #[ensures(a.op(b).and_then_logic(|ab: Self| ab.op(c)) == b.op(c).and_then_logic(|bc| a.op(bc)))]
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
    #[requires(i.op(i) == Some(i))]
    #[requires(i.op(self) == Some(self))]
    #[ensures(match self.core() {
        Some(c) => i.incl(c),
        None => false,
    })]
    fn core_is_maximal_idemp(self, i: Self) {}
}

impl UnitRA for Nat {
    #[logic(open, inline)]
    #[ensures(forall<x: Self> #[trigger(x.op(result))] x.op(result) == Some(x))]
    fn unit() -> Self {
        let _ = Nat::ext_eq;
        Nat::new(0)
    }

    #[logic(open, inline)]
    #[ensures(self.core() == Some(result))]
    fn core_total(self) -> Self {
        Nat::new(0)
    }

    #[logic]
    #[ensures(self.core_total().op(self.core_total()) == Some(self.core_total()))]
    #[ensures(self.core_total().op(self) == Some(self))]
    fn core_total_idemp(self) {
        let _ = Nat::ext_eq;
    }
}
