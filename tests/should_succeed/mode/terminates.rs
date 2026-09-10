extern crate creusot_std;
use creusot_std::prelude::*;

#[check(terminates)]
#[requires(|mode| mode.terminates() ==> x@ > 0)]
pub fn f(x: usize) {}

pub fn g() {
    f(0)
}
