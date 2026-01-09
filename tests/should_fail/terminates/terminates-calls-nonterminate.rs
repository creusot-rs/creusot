#![allow(unused)]
extern crate creusot_std;
use creusot_std::prelude::*;

#[check(terminates)]
fn i_terminate() {
    i_dont();
}

fn i_dont() {}
