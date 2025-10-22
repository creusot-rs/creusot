extern crate creusot_contracts;
use creusot_contracts::prelude::*;

pub fn capture_non_copy_data(v: Vec<i32>) {
    ghost!(v);
}
