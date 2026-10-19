extern crate creusot_std;
use creusot_std::prelude::*;

#[logic]
#[requires(true)]
pub fn foo() {
    let i = 0x1234567890abcdef000FEDCBA0987654321;
    let j = 99114423091819531172504291514877162636065;
    proof_assert!(i == j);
    proof_assert!(i > u128::MAX@);
    proof_assert!(j > u128::MAX@);
}
