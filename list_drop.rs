#![feature(register_tool)]
#![register_tool(creusot)]
extern crate creusot_contracts;
use creusot_contracts::*;

// This test verifies that when we drop an owned pointer which internally holds a mutable reference
// we collect the correct assumptions.

struct List<T> {
    hd: T,
    tl: Option<Box<List<T>>>
}

// #[ensures(^ p.0 == * p.0)]
// #[ensures(^ p.1 == * p.1)]
// #[ensures({let (a, b) = ^ p; true})]
fn should_drop_pair(p: (&mut u32, &mut u32)) {}

fn should_drop_list(t: List<&mut u32>) {
}

fn main() {}
