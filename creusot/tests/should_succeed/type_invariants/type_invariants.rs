extern crate creusot_contracts;
use creusot_contracts::*;

pub struct WithInvariant;

impl WithInvariant {
    #[predicate]
    #[creusot::type_invariant]
    fn invariant(self) -> bool {
        true
    }
}

pub fn id(x: WithInvariant) -> WithInvariant {
    x
}