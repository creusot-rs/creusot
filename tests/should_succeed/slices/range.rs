extern crate creusot_std;
use creusot_std::prelude::*;

#[requires(a@ == seq![0u32, 0u32, 0u32, 0u32])]
#[ensures((^a)@ == seq![0u32, 1u32, 1u32, 0u32])]
pub fn slice_range_inclusive(a: &mut [u32]) {
    let s = &mut a[1..=2];
    s[0] = 1;
    s[1] = 1;
}
