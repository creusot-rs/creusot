use crate::macros::*;

pub trait Invariant {
    #[predicate]
    fn invariant(self) -> bool;
}
