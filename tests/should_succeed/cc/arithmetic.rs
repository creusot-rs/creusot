extern crate creusot_contracts;
use creusot_contracts::{logic::ops::NthBitLogic as _, *};

#[bitwise_proof]
pub fn test() {
    proof_assert!(0u8.nth_bit(42) == false);
    proof_assert!(42u8.nth_bit(0) == false);
    proof_assert!(42u8.nth_bit(1) == true);
}
