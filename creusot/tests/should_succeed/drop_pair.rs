#![feature(register_tool)]
#![register_tool(creusot)]
extern crate creusot_contracts;
use creusot_contracts::*;

fn main () {}

// Fix spec parser!
// #[ensures(^ x.0 == * x.0)]
// #[ensures(^ x.1 == * x.1)]
fn drop_pair(x : (&mut u32, &mut u32)) {
}

fn drop_pair2(x : (&mut u32, &mut u32)) { x;
}
