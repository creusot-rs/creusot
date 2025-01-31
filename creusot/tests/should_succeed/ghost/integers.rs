extern crate creusot_contracts;
use creusot_contracts::*;

pub fn in_ghost_block() {
    let x = ghost!(1int);
    ghost! {
        let y = 2int;
        let z = *x + y;
        let w = z * 3int;
        proof_assert!(w == 9);
    };

    ghost! {
        let x = ghost_function(4int, 13int, 5int);
        proof_assert!(x == 7);
    };
}

#[pure]
#[ensures(result == x + y % z)]
pub fn ghost_function(x: Int, y: Int, z: Int) -> Int {
    x + y % z
}
