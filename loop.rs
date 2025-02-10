extern crate creusot_contracts;
use creusot_contracts::*;

fn example() -> bool {
    let mut j = 0;
    let loop_len = 5;
    #[invariant( 0usize <= j && j <= loop_len)]
    while 0 < 5 {
        return true;
    }
    return true;
}
