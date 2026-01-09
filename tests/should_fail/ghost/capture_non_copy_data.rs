extern crate creusot_std;
use creusot_std::prelude::*;

pub fn capture_non_copy_data(v: Vec<i32>) {
    ghost!(v);
}
