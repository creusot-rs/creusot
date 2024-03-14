extern crate creusot_contracts;

use creusot_contracts::{logic::Int, *};

#[ensures(forall<i : Int> 0 <= i && i < (^v)@.len() ==> (^v)[i] == 0u32)]
#[ensures(v@.len() == (^v)@.len())]
pub fn all_zero(v: &mut Vec<u32>) {
    let old_v = snapshot! { v };
    #[invariant(v@.len() == old_v@.len())]
    #[invariant(forall<j : Int> 0 <= j && j < produced.len() ==> v[j] == 0u32)]
    for i in 0..v.len() {
        v[i] = 0;
    }
}
