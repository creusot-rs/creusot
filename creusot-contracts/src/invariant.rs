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

impl<'a, T: Invariant + ?Sized> Invariant for &'a T {
    #[predicate]
    #[creusot::ignore_type_invariant = "maybe"]
    fn invariant(self) -> bool {
        pearlite! { (*self).invariant() }
    }
}

impl<'a, T: Invariant + ?Sized> Invariant for &'a mut T {
    #[predicate]
    #[creusot::ignore_type_invariant = "maybe"]
    fn invariant(self) -> bool {
        pearlite! { (*self).invariant() }
    }
}

impl<T: Invariant + ?Sized> Invariant for Box<T> {
    #[predicate]
    #[creusot::ignore_type_invariant = "maybe"]
    fn invariant(self) -> bool {
        pearlite! { (*self).invariant() }
    }
}

impl<T: Invariant, U: Invariant> Invariant for (T, U) {
    #[predicate]
    #[creusot::ignore_type_invariant = "maybe"]
    fn invariant(self) -> bool {
        pearlite! { self.0.invariant() && self.1.invariant() }
    }
}

impl<T: Invariant> Invariant for Option<T> {
    #[predicate]
    #[creusot::ignore_type_invariant = "maybe"]
    fn invariant(self) -> bool {
        pearlite! {
            match self {
                Some(x) => x.invariant(),
                None => true,
            }
        }
    }
}
