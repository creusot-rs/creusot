use crate::*;

#[rustc_diagnostic_item = "creusot_invariant"]
pub trait Invariant {
    #[predicate]
    #[rustc_diagnostic_item = "creusot_invariant_method"]
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

impl<'a, T: Invariant> Invariant for &'a mut T {
    #[predicate]
    fn invariant(self) -> bool {
        pearlite! { (*self).invariant() && (^self).invariant() }
    }
}
