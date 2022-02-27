extern crate creusot_contracts;

use creusot_contracts::std::*;
use creusot_contracts::*;

fn slice_arg(a: &[u32]) -> u32 {
    // a[10]
    0
}

#[requires(10 < (@a).len() && (@a).len() <= 100)]
fn index_slice(a: &[u32]) -> u32 {
    a[10]
}

// #[requires((@a).len() === 5)]
// fn index_mut_slice(a: &mut [u32]) {
//     a[2] = 3;
// }
