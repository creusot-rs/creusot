extern crate creusot_contracts;

use creusot_contracts::*;

// Bug #181
#[logic]
fn max_Int(a: Int, b: Int) -> Int {
    if a < b {
        b
    } else {
        a
    }
}

#[trusted]
#[ensures(@result === max_Int(@a, @b))]
fn max_usize(a: usize, b: usize) -> usize {
    if a < b {
        b
    } else {
        a
    }
}
