extern crate creusot_contracts;

use creusot_contracts::*;

fn test_invariant_move(mut x: Vec<u32>) {
    #[invariant(dummy, x == x)]
    while let Some(x) = { (&mut x).pop() } {}
}
