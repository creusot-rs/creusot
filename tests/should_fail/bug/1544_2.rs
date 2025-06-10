extern crate creusot_contracts;
use creusot_contracts::PartialEq;

pub trait One {
    fn one() -> Self;

    fn is_one(&self) -> bool {
        true
    }
}

#[derive(PartialEq)]
pub struct Base(i32);

impl One for Base {
    fn one() -> Self {
        Self(1)
    }

    fn is_one(&self) -> bool
    where
        // This line was to blame for an ICE!!! This used to crash the purity test,
        // when trying to specialize a trait function.
        Self: PartialEq,
    {
        *self == Self::one()
    }
}
