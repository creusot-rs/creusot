use crate::*;

pub trait Invariant {
    #[predicate]
    #[open]
    #[rustc_diagnostic_item = "creusot_invariant_user"]
    fn invariant(self) -> bool {
        true
    }
}

#[predicate]
#[open(self)]
#[rustc_diagnostic_item = "creusot_invariant_internal"]
pub fn inv<T>(_x: T) -> bool {
    true
}
