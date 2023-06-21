#![allow(incomplete_features)]
#![feature(specialization)]
extern crate creusot_contracts;
use creusot_contracts::{invariant::Invariant, *};

pub struct NonZeroU32(u32);

impl Invariant for NonZeroU32 {
    #[open]
    #[predicate]
    fn invariant(self) -> bool {
        pearlite! { self.0@ > 0 }
    }
}

impl NonZeroU32 {
    #[requires(n@ > 0)]
    #[ensures(result.0 == n)]
    pub fn new(n: u32) -> Self {
        Self(n)
    }

    #[requires(self.0@ > rhs.0@)]
    #[ensures((^self).0@ == (*self).0@ - rhs.0@)]
    pub fn sub_mut(&mut self, rhs: Self) {
        self.0 -= rhs.0;
    }
}

#[requires(n.0@ > 1)]
pub fn dec(mut n: NonZeroU32) -> NonZeroU32 {
    let borrowed = &mut n;
    borrowed.sub_mut(NonZeroU32::new(1));
    n
}
