#![allow(unused)]
extern crate creusot_contracts;
use creusot_contracts::*;

#[check(terminates)]
fn terminates_while_loop() {
    #[allow(while_true)]
    while true {}
}

#[check(terminates)]
fn terminates_loop_loop() {
    loop {}
}
