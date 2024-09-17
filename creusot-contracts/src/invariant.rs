use crate::*;

pub trait Invariant {
    #[predicate(prophetic)]
    #[open]
    #[rustc_diagnostic_item = "creusot_invariant_user"]
    fn invariant(self) -> bool {
        true
    }
}

impl Invariant for ! {
    #[predicate(prophetic)]
    #[open]
    #[creusot::trusted_ignore_structural_inv]
    fn invariant(self) -> bool {
        false
    }
}

impl<T: ?Sized> Invariant for &T {
    #[predicate(prophetic)]
    #[open]
    #[creusot::trusted_ignore_structural_inv]
    fn invariant(self) -> bool {
        inv(*self)
    }
}

impl<T: ?Sized> Invariant for &mut T {
    #[predicate(prophetic)]
    #[open]
    #[creusot::trusted_ignore_structural_inv]
    fn invariant(self) -> bool {
        pearlite! { inv(*self) && inv(^self) }
    }
}

#[predicate(prophetic)]
#[open(self)]
#[rustc_diagnostic_item = "creusot_invariant_internal"]
pub fn inv<T: ?Sized>(_: T) -> bool {
    true
}
