use crate::*;

#[rustc_diagnostic_item = "creusot_invariant"]
pub trait Invariant {
    #[predicate]
    #[rustc_diagnostic_item = "creusot_invariant_method"]
    #[creusot::type_invariant]
    fn invariant(self) -> bool {
        true
    }

    #[law]
    #[ensures(exists<x: Self> x.invariant())]
    #[ensures(result)]
    fn is_inhabited() -> bool
    where
        Self: Sized,
    {
        true
    }
}
