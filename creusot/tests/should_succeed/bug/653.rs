#![no_std]
extern crate creusot_contracts;
use creusot_contracts::*;

#[ensures(@result == @n * (@n + 1) / 2)]
pub fn omg(n: usize) -> usize {
    n
}
