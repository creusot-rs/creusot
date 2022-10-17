use crate::*;

pub trait Invariant {
    #[predicate]
    fn invariant(self) -> bool;
}
