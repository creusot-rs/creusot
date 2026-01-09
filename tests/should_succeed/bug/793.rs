extern crate creusot_std;
use creusot_std::prelude::*;

#[requires(x@ < u32::MAX@ / 1)]
pub fn div_err(f: f64, x: u32) {}
