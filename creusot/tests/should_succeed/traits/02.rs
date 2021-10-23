// SHOULD_SUCCEED: parse-print
extern crate creusot_contracts;
use creusot_contracts::*;

trait A {
    #[ensures(result == true)]
    fn is_true(&self) -> bool;
}

#[ensures(result == true)]
fn omg<T: A>(a: T) -> bool {
    a.is_true()
}
