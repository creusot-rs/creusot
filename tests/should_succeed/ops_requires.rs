extern crate creusot_std;
use creusot_std::{logic::ops::*, prelude::*};

pub struct Seq {
    pub inner: creusot_std::logic::Seq<()>,
}

pub struct Nat {
    pub inner: creusot_std::logic::Nat,
}

impl SubLogic for Nat {
    type Output = Self;

    #[logic(open)]
    #[requires(self.inner >= other.inner)]
    fn sub_logic(self, other: Self) -> Self::Output {
        Self { inner: creusot_std::logic::Nat::new(self.inner.to_int() - other.inner.to_int()) }
    }
}

impl IndexLogic<Nat> for Seq {
    type Item = ();

    #[logic(open)]
    #[requires(idx.inner.to_int() < self.inner.len())]
    fn index_logic(self, idx: Nat) -> () {
        self.inner[idx.inner.to_int()]
    }
}

#[logic]
#[requires(seq.inner.len() > 0)]
pub fn test_index(seq: Seq) {
    seq[Nat { inner: creusot_std::logic::Nat::new(0) }]
}

#[logic]
#[requires(true)]
pub fn test_sub() -> Nat {
    let a = Nat { inner: creusot_std::logic::Nat::new(1) };
    let b = Nat { inner: creusot_std::logic::Nat::new(0) };
    a - b
}
