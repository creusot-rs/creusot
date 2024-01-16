extern crate creusot_contracts;
use creusot_contracts::{invariant::Invariant, *};

pub struct SumTo10 {
    a: i32,
    b: i32,
}

impl Invariant for SumTo10 {
    #[open]
    #[predicate]
    fn invariant(self) -> bool {
        true
    }
}

pub fn vec(x: Vec<&mut SumTo10>) {
}
