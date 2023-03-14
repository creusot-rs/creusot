use crate::*;

pub trait Invariant {
    #[predicate]
    fn invariant(self) -> bool;
}

pub trait Invariant2 {
    #[predicate]
    fn invariant(self) -> bool {
        true
    }
}
