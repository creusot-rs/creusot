#![allow(unused)]
extern crate creusot_contracts;
use creusot_contracts::*;

#[check(terminates)]
fn i_terminate() {
    i_dont();
}

fn i_dont() {}
