extern crate creusot_std;
use creusot_std::{invariant::Invariant, prelude::*};

pub struct WithInvariant;

impl Invariant for WithInvariant {
    #[logic(open)]
    fn invariant(self) -> bool {
        true
    }
}

pub fn id(x: WithInvariant) -> WithInvariant {
    x
}
