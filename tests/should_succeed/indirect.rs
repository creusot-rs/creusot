extern crate creusot_std;
use creusot_std::prelude::*;

#[logic(indirect)]
#[allow(unused)]
pub fn indirect() -> Int {
    3
}

#[logic]
#[ensures(result == 3)]
pub fn use_indirect() -> Int {
    indirect()
}
