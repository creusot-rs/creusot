extern crate creusot_std;
use creusot_std::prelude::*;

#[trusted]
pub trait Trusted {}

impl Trusted for () {}

pub trait HasPredicate {
    #[logic(open(self))]
    fn my_predicate() -> bool {
        true
    }
}

impl HasPredicate for u32 {
    fn my_predicate() -> bool {
        false
    }
}
