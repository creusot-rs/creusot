// WHY3PROVE Z3

extern crate creusot_contracts;
use creusot_contracts::*;

// Verifies that implementations can refine the contract of their encompassing trait

trait Tr {
    #[ensures(@result >= 10)]
    fn my_function(&self) -> usize;
}

impl Tr for () {
    #[requires(true)]
    #[ensures(@result >= 15)]
    fn my_function(&self) -> usize {
        20
    }
}
