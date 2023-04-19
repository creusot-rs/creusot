extern crate creusot_contracts;

use creusot_contracts::*;

#[trusted]
#[requires(@l <= @u)]
#[ensures(@l <= @result && @result  < @u)]
fn rand_in_range(l: usize, u: usize) -> usize {
    panic!()
}

#[ensures((@^v).permutation_of(@v))]
pub fn knuth_shuffle<T>(v: &mut Vec<T>) {
    let old_v = ghost! { v };

    #[invariant(permutation, v@.permutation_of(@old_v))]
    for n in 0..v.len() {
        // We assign the length to a variable to work around a limitation with two-phase borrows
        // where we forget the value stored in the reference.
        let upper = v.len() - n;
        let i = rand_in_range(0, upper);
        v.swap(i, upper - 1);
    }
}
