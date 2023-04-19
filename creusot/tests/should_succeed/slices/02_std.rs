// test some extern specs on slcies
extern crate creusot_contracts;

use creusot_contracts::*;

#[requires(forall<i : _> 0 <= i && i < s@.len() ==> s[i]@ == i)]
#[requires(s@.len() == 5)]
pub fn binary_search(s: &[u32]) -> usize {
    let ix = s.binary_search(&2).unwrap();

    proof_assert! { ix@ < 5 };
    ix
}
