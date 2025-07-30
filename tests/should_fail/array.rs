extern crate creusot_contracts;
use creusot_contracts::*;

fn main() {
    let _ = [0; 8];
}

// Checks that array expressions are not allowed in specificatiosn
#[requires([0, 1, 2, 3] == x)]
fn array_in_spec(x: [u32; 4]) {}

// Checks that array reptitions are not allowed in specificatiosn
#[requires([0; 4] == x)]
fn repeat_in_spec(x: [u32; 4]) {}
