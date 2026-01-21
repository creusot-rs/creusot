extern crate creusot_std;
use creusot_std::prelude::*;

pub const USIZE_BITS: usize = std::mem::size_of::<usize>() * 8;

#[ensures(result == ffs_logic(val))]
pub fn ffs(val: usize) -> u32 {
    USIZE_BITS as u32 - val.leading_zeros()
}

#[logic]
pub fn ffs_logic(val: usize) -> u32 {
    pearlite! {
        USIZE_BITS as u32 - val.leading_zeros_logic()
    }
}

#[bitwise_proof]
#[ensures(val == 0usize ==> result == val)]
#[ensures(val != 0usize ==> result == val & !(1usize << (ffs_logic(val) - 1u32)))]
pub fn empty(val: usize) -> usize {
    let rq_ffs = ffs(val);
    if rq_ffs == 0 {
        0
    } else {
        let rq = (rq_ffs - 1) as u8;
        val & !(1 << rq)
    }
}

#[logic]
pub fn has_bit(bitvec: usize, bit: u8) -> bool {
    bitvec & (1usize << bit) != 0usize
}

#[bitwise_proof]
#[requires(bit@ < USIZE_BITS@)]
#[ensures(has_bit(result, bit))]
#[ensures(forall<b: u8> has_bit(bitvec, b) ==> has_bit(result, b))]
pub fn set_bit(bitvec: usize, bit: u8) -> usize {
    bitvec | (1 << bit)
}

#[bitwise_proof]
#[requires(bit@ < USIZE_BITS@)]
#[ensures(!has_bit(result, bit))]
#[ensures(forall<b: u8> b != bit && has_bit(bitvec, b) ==> has_bit(result, b))]
pub fn unset_bit(bitvec: usize, bit: u8) -> usize {
    bitvec & !(1 << bit)
}

#[bitwise_proof]
#[ensures(forall<b: u8> has_bit(lhs, b) ==> has_bit(result, b))]
#[ensures(forall<b: u8> has_bit(rhs, b) ==> has_bit(result, b))]
pub fn merge_bvs(lhs: usize, rhs: usize) -> usize {
    lhs | rhs
}
