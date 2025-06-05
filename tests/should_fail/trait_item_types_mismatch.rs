extern crate creusot_contracts;
use creusot_contracts::*;

#[trusted]
pub trait Trusted {}

impl Trusted for () {}

pub trait HasPredicate {
    #[predicate]
    #[open(self)]
    fn my_predicate() -> bool {
        true
    }
}

impl HasPredicate for u32 {
    fn my_predicate() -> bool {
        false
    }
}
