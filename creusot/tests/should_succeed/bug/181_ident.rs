extern crate creusot_contracts;

use creusot_contracts::{logic::Int, *};

// Bug #181
#[logic]
#[open]
pub fn max_int(a: Int, b: Int) -> Int {
    if a < b {
        b
    } else {
        a
    }
}

#[trusted]
#[ensures(result@ == max_int(a@, b@))]
pub fn max_usize(a: usize, b: usize) -> usize {
    if a < b {
        b
    } else {
        a
    }
}
