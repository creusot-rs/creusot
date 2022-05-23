extern crate creusot_contracts;
use creusot_contracts::*;

#[logic]
#[creusot::decl::opaque]
#[ensures(result == 2)]
fn two() -> Int {
    pearlite! {
     1 + 1 - 1 + 1 - 1 + 1 - 1 + 1
    }
}

#[ensures(@result == two())]
fn x() -> u64 {
    2
}
