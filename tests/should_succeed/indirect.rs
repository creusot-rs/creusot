extern crate creusot_std;
use creusot_std::prelude::*;

#[logic(indirect)]
pub fn indirect() -> Int {
    3
}

#[logic(#[trigger(x + 1)] indirect)]
pub fn indirect_trig(x: Int) -> Int {
    x
}

#[logic]
#[ensures(result == 3)]
pub fn use_indirect() -> Int {
    indirect() + indirect_trig(0)
}
