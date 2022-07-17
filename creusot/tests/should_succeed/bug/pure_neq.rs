extern crate creusot_contracts;
use creusot_contracts::*;

#[logic]
#[ensures(result == !(x == y))]
pub fn f(x: Option<Int>, y: Option<Int>) -> bool {
    pearlite! { x != y }
}
