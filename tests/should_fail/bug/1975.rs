extern crate creusot_std;
use creusot_std::prelude::*;

#[opaque]
pub struct Zero;

pub fn zero() -> Zero {
    Zero
}

pub fn nil(x: Zero) {
    match x {
        Zero => {}
    }
}

#[logic]
pub fn zilch() -> Zero {
    Zero
}

#[opaque]
pub struct One(());

pub fn one(_x: One) {
    _x.0
}
