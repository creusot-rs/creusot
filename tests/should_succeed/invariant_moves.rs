extern crate creusot_std;

use creusot_std::prelude::*;

pub fn test_invariant_move(mut x: Vec<u32>) {
    #[invariant(x == x)]
    while let Some(_) = { (&mut x).pop() } {}
}
