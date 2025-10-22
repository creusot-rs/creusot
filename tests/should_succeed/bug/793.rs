extern crate creusot_contracts;
use creusot_contracts::prelude::*;

#[requires(x@ < u32::MAX@ / 1)]
pub fn div_err(f: f64, x: u32) {}
