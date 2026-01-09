extern crate creusot_std;
use creusot_std::{invariant::Invariant, prelude::*};

pub struct WithInvariant;

impl Invariant for WithInvariant {
    #[logic(open)]
    fn invariant(self) -> bool {
        true
    }
}

#[logic(open)]
#[ensures(forall<x: WithInvariant> x.invariant())]
pub fn forall() {}

#[logic(open)]
#[ensures(exists<_x: WithInvariant> true)]
pub fn exists() {}
