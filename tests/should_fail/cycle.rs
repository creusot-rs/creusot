extern crate creusot_std;
use creusot_std::prelude::*;

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
