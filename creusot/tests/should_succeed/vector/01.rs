extern crate creusot_contracts;

use creusot_contracts::{logic::Int, *};

#[ensures(forall<i : Int> 0 <= i && i < (^v)@.len() ==> (^v)@[i] == 0u32)]
#[ensures(v@.len() == (^v)@.len())]
pub fn all_zero(v: &mut Vec<u32>) {
    let old_v = ghost! { v };
    // This invariant is because why3 can't determine that the prophecy isn't modified by the loop
    // Either Why3 or Creusot should be improved to do this automaticallly (probably why3)
    #[invariant(in_bounds, v@.len() == old_v@.len())]
    #[invariant(all_zero, forall<j : Int> 0 <= j && j < produced.len() ==> v@[j] == 0u32)]
    for i in 0..v.len() {
        v[i] = 0;
    }
}
