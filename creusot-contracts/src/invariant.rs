use crate::*;

pub trait Invariant {
    #[predicate]
    #[rustc_diagnostic_item = "creusot_invariant_user"]
    fn invariant(self) -> bool;

    #[law]
    #[ensures(exists<x: Self> x.invariant())]
    #[ensures(result)]
    fn is_inhabited() -> bool
    where
        Self: Sized;
}

impl<T> Invariant for T {
    #[predicate]
    #[open]
    #[rustc_diagnostic_item = "creusot_invariant_user_default"]
    default fn invariant(self) -> bool {
        true
    }

    #[law]
    #[open]
    #[ensures(exists<x: Self> x.invariant())]
    #[ensures(result)]
    default fn is_inhabited() -> bool
    where
        Self: Sized,
    {
        true
    }
}

#[predicate]
#[open(self)]
#[rustc_diagnostic_item = "creusot_invariant_internal"]
pub fn inv<T>(_x: T) -> bool {
    true
}
