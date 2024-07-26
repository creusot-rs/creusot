extern crate creusot_contracts;
use creusot_contracts::*;

// Prove that after the call to this function the vector only contains zeroes
// Also show that no elements were added or removed
pub fn all_zero(v: &mut Vec<u32>) {
    let mut i = 0;
    let old_v = snapshot! { v };

    while i < v.len() {
        v[i] = 0;
        i += 1;
    }
}
