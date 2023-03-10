extern crate creusot_contracts;
use creusot_contracts::{*, invariant::Invariant};

pub struct WithInvariant;

impl Invariant for WithInvariant {
    #[predicate]
    #[creusot::type_invariant]
    fn invariant(self) -> bool {
        true
    }
}

#[law]
#[ensures(forall<x: WithInvariant> x.invariant())]
pub fn forall() {}

#[law]
#[ensures(exists<_x: WithInvariant> true)]
pub fn exists() {}
