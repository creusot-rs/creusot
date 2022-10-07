extern crate creusot_contracts;
use creusot_contracts::*;

#[requires(@x == 100_000)]
pub fn test_fnmut(mut x: u32) {
    let mut c = {
        #[requires(@x < 1_000_000)]
        #[ensures(@x == @old(x) + 1)]
        || {
            x += 1;
            5
        }
    };
    c();
    c();

    proof_assert! { @x == 100_002};
}
