use crate::*;

#[rustc_diagnostic_item = "creusot_invariant"]
pub trait Invariant {
    #[predicate]
    #[rustc_diagnostic_item = "creusot_invariant_method"]
    fn invariant(self) -> bool;
}
