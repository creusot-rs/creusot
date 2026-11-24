use crate::{
    logic::ra::{RA, UnitRA, update::LocalUpdate},
    prelude::*,
};

impl RA for Int {
    #[logic(open, inline)]
    fn op(self, other: Self) -> Option<Int> {
        Some(self + other)
    }

    #[logic(open)]
    #[allow(unused_variables)]
    fn incl(self, other: Self) -> bool {
        true
    }

    #[logic(law)]
    #[allow(unused_variables)]
    fn commutative(a: Self, b: Self) {}

    #[logic]
    #[allow(unused_variables)]
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
    #[allow(unused_variables)]
    fn core_is_maximal_idemp(self, i: Self) {}

    #[logic(open)]
    fn cancelable(self) -> bool {
        true
    }
}

impl UnitRA for Int {
    #[logic(open, inline)]
    fn unit() -> Self {
        0
    }

    #[logic(open, inline)]
    fn core_total(self) -> Self {
        0
    }

    #[logic]
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
