use crate::*;

#[rustc_diagnostic_item = "creusot_invariant"]
pub trait Invariant {
    #[predicate]
    #[open]
    #[rustc_diagnostic_item = "creusot_invariant_method"]
    fn invariant(self) -> bool {
        true
    }

    #[law]
    #[open]
    #[ensures(exists<x: Self> x.invariant())]
    #[ensures(result)]
    fn is_inhabited() -> bool
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

pub trait UserInv {
    #[predicate]
    #[rustc_diagnostic_item = "creusot_invariant_user"]
    fn user_inv(self) -> bool;
}

#[cfg(creusot)]
impl<T> UserInv for T {
    #[predicate]
    #[open]
    #[rustc_diagnostic_item = "creusot_invariant_user_default"]
    default fn user_inv(self) -> bool {
        true
    }
}

impl<'a, T: Invariant + ?Sized> Invariant for &'a T {
    #[predicate]
    #[open]
    fn invariant(self) -> bool {
        pearlite! { (*self).invariant() }
    }
}

impl<'a, T: Invariant + ?Sized> Invariant for &'a mut T {
    #[predicate]
    #[open]
    fn invariant(self) -> bool {
        pearlite! { (*self).invariant() }
    }
}

impl<T: Invariant + ?Sized> Invariant for Box<T> {
    #[predicate]
    #[open]
    fn invariant(self) -> bool {
        pearlite! { (*self).invariant() }
    }
}

impl<T: Invariant, U: Invariant> Invariant for (T, U) {
    #[predicate]
    #[open]
    fn invariant(self) -> bool {
        pearlite! { self.0.invariant() && self.1.invariant() }
    }
}

impl<T: Invariant> Invariant for Option<T> {
    #[predicate]
    #[open]
    fn invariant(self) -> bool {
        pearlite! {
            match self {
                Some(x) => x.invariant(),
                None => true,
            }
        }
    }
}
