extern crate creusot_contracts;
use creusot_contracts::*;

pub fn f() {
    g(true);
}

pub fn g(x: bool) {
    if x {
        f();
    }
}
