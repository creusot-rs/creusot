extern crate creusot_contracts;
use creusot_contracts::*;

#[terminates]
fn terminating() {}

pub fn calls_terminating() {
    ghost! {
        terminating();
    };
}
