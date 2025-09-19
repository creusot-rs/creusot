extern crate creusot_contracts;
use creusot_contracts::{invariant::Invariant, *};

pub struct WithInvariant;

impl Invariant for WithInvariant {
    #[logic(open)]
    fn invariant(self) -> bool {
        true
    }
}

#[logic(open, law)]
#[ensures(forall<x: WithInvariant> x.invariant())]
pub fn forall() {}

#[logic(open, law)]
#[ensures(exists<_x: WithInvariant> true)]
pub fn exists() {}
