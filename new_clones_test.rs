extern crate creusot_contracts;
use creusot_contracts::{std::iter::*, *};

pub fn counter(v: Vec<u32>) {
    let x: Vec<u32> = v.iter().map_inv(|x, _prod| 0).collect();
}
