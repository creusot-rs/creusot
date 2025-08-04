extern crate creusot_contracts;
use creusot_contracts::*;

#[check(terminates)]
fn terminating() {}

pub fn calls_terminating() {
    ghost! {
        terminating();
    };
}
