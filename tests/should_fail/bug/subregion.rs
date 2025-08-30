// WHY3PROVE
extern crate creusot_contracts;
use creusot_contracts::*;
pub fn list_reversal_h(l: usize) -> usize {
    let mut r = 0;
    #[invariant(true)]
    while l != 0 {
        proof_assert!(false);
        let _x = r;
        let tmp = l;
        r = tmp;
    }
    // proof_assert!(false);
    return r;
}
