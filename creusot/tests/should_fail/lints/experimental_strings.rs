extern crate creusot_contracts;
use creusot_contracts::*;

#[deny(creusot::experimental)]
#[requires(true)]
pub fn f() {
    let _s = "Hello world";
}
