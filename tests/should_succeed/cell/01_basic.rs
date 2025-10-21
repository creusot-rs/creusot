extern crate creusot_contracts;

use creusot_contracts::{cell::PredCell, prelude::*};

#[requires(c@ == |z: u32| z@ % 2 == 0)]
pub fn adds_two(c: &PredCell<u32>) {
    let v = c.get();

    // To shut up overflow checking
    if v < 100000 {
        c.set(v + 2);
    } else {
        c.set(0);
    }
}
