extern crate creusot_contracts;

use creusot_contracts::std::*;
use creusot_contracts::*;

// fn slice_arg(a: &[u32]) -> u32 {
//     // a[10]
//     0
// }

// #[requires(10 < (@a).len() && (@a).len() <= 100)]
// fn index_slice(a: &[u32]) -> u32 {
//     a[10]
// }

// #[requires((@a).len() == 5)]
// #[ensures(@((@^a)[2]) == 3)]
// fn index_mut_slice(a: &mut [u32]) {
//     a[2] = 3;
// }

// #[ensures(match result {
//     Some(v) => *v == (@a)[0],
//     None => (@a).len() == 0
// })]
fn slice_first<T>(a: &[T]) -> Option<&T> {
    if a.len() > 0 {
        Some(&a[0])
    } else {
        None
    }
}
