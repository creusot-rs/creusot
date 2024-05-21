#![allow(unused)]
extern crate creusot_contracts;
use creusot_contracts::*;

mod m {
    #[super::terminates]
    pub fn f1() {
        super::f2();
    }
}

#[terminates]
fn f2() {
    f3();
}

#[terminates]
fn f3() {
    m::f1();
}
