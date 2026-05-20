extern crate creusot_std;
use creusot_std::prelude::*;

#[check(terminates)]
#[requires(i@ >= 0)]
#[variant(i)]
pub fn count_paths(i: isize) {
    let _ = (0..i).map(|j| count_paths(j));
}
