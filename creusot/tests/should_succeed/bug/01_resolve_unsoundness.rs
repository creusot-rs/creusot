// UNBOUNDED UNSTABLE

#![feature(type_ascription)]

extern crate creusot_contracts;

use creusot_contracts::*;

// This program exhibited a bug where we resolve the borrow of `push`, causing
// us to prove an invalid loop invariant
// This program should not prove.
#[ensures((@result).len() == @n)]
pub fn make_vec_of_size(n: usize) -> Vec<bool> {
    let mut out: Vec<bool> = Vec::new();
    let mut i = 0;
    #[invariant(loop_invariant, 0usize <= i && i <= n)]
    while i <= n {
        out.push(false);
        i += 1
    }
    return out;
}
