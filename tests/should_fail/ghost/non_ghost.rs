extern crate creusot_contracts;
use creusot_contracts::*;

#[safety(terminates)]
fn terminating() {}

pub fn calls_terminating() {
    ghost! {
        terminating();
    };
}
