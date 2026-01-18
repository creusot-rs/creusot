extern crate creusot_std;

use creusot_std::prelude::*;

#[trusted]
#[requires(l@ <= u@)]
#[ensures(l@ <= result@ && result@  < u@)]
fn rand_in_range(l: usize, u: usize) -> usize {
    panic!()
}

#[ensures((^v)@.permutation_of(v@))]
pub fn knuth_shuffle<T>(v: &mut Vec<T>) {
    let old_v = snapshot! { v };

    #[invariant(v@.permutation_of(old_v@))]
    for n in 0..v.len() {
        let upper = v.len() - n;
        let i = rand_in_range(0, upper);
        v.swap(i, upper - 1);
    }
}
