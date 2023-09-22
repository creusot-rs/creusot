extern crate creusot_contracts;
use creusot_contracts::{invariant::Invariant, *};

pub struct Sum10(i32, i32);

impl Invariant for Sum10 {
    #[predicate]
    #[open]
    fn invariant(self) -> bool {
        pearlite! { self.0@ + self.1@ == 10 }
    }
}

pub fn take_array<const N: usize>(a: [Sum10; N]) -> [Sum10; N] {
    a
}

pub fn test_array() {
    let x = Sum10(3, 7);
    let a = [x];
    take_array(a);
}
