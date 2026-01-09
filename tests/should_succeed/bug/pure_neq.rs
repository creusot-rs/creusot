extern crate creusot_std;
use creusot_std::{logic::Int, prelude::*};

#[logic(open)]
#[ensures(result == !(x == y))]
pub fn f(x: Option<Int>, y: Option<Int>) -> bool {
    pearlite! { x != y }
}
