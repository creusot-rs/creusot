extern crate creusot_std;
use creusot_std::{logic::ops::NthBitLogic as _, prelude::*};

#[bitwise_proof]
pub fn test() {
    proof_assert!(0u8.nth_bit(42) == false);
    proof_assert!(42u8.nth_bit(0) == false);
    proof_assert!(42u8.nth_bit(1) == true);
}

#[bitwise_proof]
#[ensures(result == *a & 0xf_u8)]
#[ensures(result@ <= 0xf)]
pub fn bitand_ref(a: &u8) -> u8 {
    a & 0xf
}

#[bitwise_proof]
#[ensures(result == *a >> 1usize)]
pub fn shr_ref(a: &u8) -> u8 {
    a >> 1
}
