extern crate creusot_std;
use creusot_std::prelude::*;

const USIZE_BITS: usize = std::mem::size_of::<usize>() * 8; 

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
