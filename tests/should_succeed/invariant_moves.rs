extern crate creusot_contracts;

use creusot_contracts::*;

pub fn test_invariant_move(mut x: Vec<u32>) {
    #[invariant(x == x)]
    while let Some(_) = { (&mut x).pop() } {}
}
