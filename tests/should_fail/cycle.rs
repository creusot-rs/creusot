extern crate creusot_contracts;
use creusot_contracts::*;

#[logic(open)]
pub fn f() {
    g(true);
}

#[logic(open)]
pub fn g(x: bool) {
    if x {
        f();
    }
}
