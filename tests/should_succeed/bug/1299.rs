extern crate creusot_std;
use creusot_std::prelude::*;

// FIXME:
// #[check(terminates)]
// #[variant(i)]
#[requires(i@ >= 0)]
pub fn count_paths(i: isize) {
    let _ = (0..i).map(|j| count_paths(j));
}
