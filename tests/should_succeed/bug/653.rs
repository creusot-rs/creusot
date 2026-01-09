// NO_REPLAY

#![no_std]
extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures(result@ == n@ * (n@ + 1) / 2)]
pub fn omg(n: usize) -> usize {
    n
}
