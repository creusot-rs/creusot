extern crate creusot_contracts;
use creusot_contracts::{*, invariant::Invariant};

pub struct NonZeroU32(u32);

impl Invariant for NonZeroU32 {
    #[predicate]
    #[creusot::type_invariant]
    fn invariant(self) -> bool {
        pearlite! { @self.0 > 0 }
    }
}

impl NonZeroU32 {
    #[requires(@n > 0)]
    pub fn new(n: u32) -> Self {
        Self(n)
    }

    #[requires(@self.0 + @rhs.0 <= @u32::MAX)]
    pub fn add(self, rhs: Self) -> Self {
        Self(self.0 + rhs.0)
    }

    #[predicate]
    pub fn sub_pre(self, rhs: Self) -> bool {
        pearlite! { @self.0 > @rhs.0 }
    }

    #[law]
    #[requires(a.sub_pre(b))]
    #[requires(b.sub_pre(c))]
    #[ensures(a.sub_pre(c))]
    pub fn sub_pre_trans(a: Self, b: Self, c: Self) {}

    #[requires(self.sub_pre(rhs))]
    pub fn sub(self, rhs: Self) -> Self {
        Self(self.0 - rhs.0)
    }
}
