extern crate creusot_std;
use creusot_std::prelude::*;

#[logic(opaque)]
pub fn works() {
    dead
}

#[logic]
pub fn fails1() {
    dead
}

#[trusted]
#[logic]
pub fn fails2() {
    dead
}
