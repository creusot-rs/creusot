use crate::{
    logic::ra::{RA, UnitRA, update::LocalUpdate},
    prelude::*,
};

impl RA for Int {
    #[logic(open, inline)]
    fn op(self, other: Self) -> Option<Int> {
        Some(self + other)
    }

    #[logic(open, inline)]
    #[ensures(match result {
        Some(c) => factor.op(c) == Some(self),
        None => false,
    })]
    fn factor(self, factor: Self) -> Option<Self> {
        Some(self - factor)
    }

    #[logic(law)]
    #[ensures(a.op(b) == b.op(a))]
    fn commutative(a: Self, b: Self) {}

    #[logic]
    #[ensures(a.op(b).and_then_logic(|ab: Self| ab.op(c)) == b.op(c).and_then_logic(|bc| a.op(bc)))]
    fn associative(a: Self, b: Self, c: Self) {}

    #[logic(open, inline)]
    fn core(self) -> Option<Self> {
        Some(0)
    }

    #[logic]
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

impl UnitRA for Int {
    #[logic(open, inline)]
    #[ensures(forall<x: Self> #[trigger(x.op(result))] x.op(result) == Some(x))]
    fn unit() -> Self {
        0
    }

    #[logic(open, inline)]
    #[ensures(self.core() == Some(result))]
    fn core_total(self) -> Self {
        0
    }

    #[logic]
    #[ensures(self.core_total().op(self.core_total()) == Some(self.core_total()))]
    #[ensures(self.core_total().op(self) == Some(self))]
    fn core_total_idemp(self) {}
}

/// Add an integer to an authority/fragment pair of integers.
impl LocalUpdate<Int> for Int {
    #[logic(open, inline)]
    fn premise(self, _: Int, _: Int) -> bool {
        true
    }

    #[logic(open, inline)]
    fn update(self, from_auth: Int, from_frag: Int) -> (Int, Int) {
        (from_auth + self, from_frag + self)
    }

    #[logic]
    #[requires(self.premise(from_auth, from_frag))]
    #[requires(Some(from_frag).op(frame) == Some(Some(from_auth)))]
    #[ensures({
        let (to_auth, to_frag) = LocalUpdate::update(self, from_auth, from_frag);
        Some(to_frag).op(frame) == Some(Some(to_auth))
    })]
    fn frame_preserving(self, from_auth: Int, from_frag: Int, frame: Option<Int>) {}
}
