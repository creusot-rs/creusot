extern crate creusot_contracts;
use creusot_contracts::*;

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
