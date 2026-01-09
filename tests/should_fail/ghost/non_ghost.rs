extern crate creusot_std;
use creusot_std::prelude::*;

#[check(terminates)]
fn terminating() {}

pub fn calls_terminating() {
    ghost! {
        terminating();
    };
}
