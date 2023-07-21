extern crate creusot_contracts;
use creusot_contracts::*;

// Prove that after the call to this function the vector only contains zeroes
// Also show that no elements were added or removed
pub fn all_zero(v: &mut Vec<u32>) {
    let mut i = 0;
    let old_v = gh! { v };
    // Until https://gitlab.inria.fr/why3/why3/-/merge_requests/667 is merged
    // the following invariant is needed to allow Why3 to remember prophecies dont change
    #[invariant(proph_const, ^v == ^old_v.inner())]
    while i < v.len() {
        v[i] = 0;
        i += 1;
    }
}
