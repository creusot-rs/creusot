extern crate creusot_contracts;
use creusot_contracts::{invariant::Invariant, *};

pub struct WithInvariant;

impl Invariant for WithInvariant {
    #[open]
    #[logic]
    fn invariant(self) -> bool {
        true
    }
}

#[law]
#[open]
#[ensures(forall<x: WithInvariant> x.invariant())]
pub fn forall() {}

#[law]
#[open]
#[ensures(exists<_x: WithInvariant> true)]
pub fn exists() {}
