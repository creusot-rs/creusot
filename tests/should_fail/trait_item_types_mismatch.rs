extern crate creusot_contracts;
use creusot_contracts::*;

#[trusted]
trait Trusted {}

impl Trusted for () {}

trait HasPredicate {
    #[predicate]
    fn my_predicate() -> bool {
        true
    }
}

impl HasPredicate for u32 {
    fn my_predicate() -> bool {
        false
    }
}
