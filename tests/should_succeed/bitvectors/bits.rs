extern crate creusot_std;
use creusot_std::prelude::*;

const USIZE_BITS: usize = std::mem::size_of::<usize>() * 8; 

#[bitwise_proof]
#[ensures((val >> result) == 0usize)]
#[ensures(result != 0u32 ==> val >> (result - 1u32) == 1usize)]
pub fn ffs(val: usize) -> u32 {
    USIZE_BITS as u32 - val.leading_zeros()
}

#[bitwise_proof]
#[ensures(val == 0usize ==> result == val)]
#[ensures(forall<rq: u32> val >> rq == 1usize ==> result >> rq == val & !(1usize << rq))]
pub fn empty(val: usize) -> usize {
    let rq_ffs = ffs(val);
    let rq = (rq_ffs - 1) as u8;
    if !rq_ffs == 0 {
        val & !(1 << rq)
    } else {
        0
    }
}
