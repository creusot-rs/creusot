#![allow(unused)]
extern crate creusot_contracts;
use creusot_contracts::*;

#[safety(terminates)]
fn terminates_while_loop() {
    #[allow(while_true)]
    while true {}
}

#[safety(terminates)]
fn terminates_loop_loop() {
    loop {}
}
