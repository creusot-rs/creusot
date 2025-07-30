#![allow(unused)]
extern crate creusot_contracts;
use creusot_contracts::*;

mod m {
    #[super::safety(terminates)]
    pub fn f1() {
        super::f2();
    }
}

#[safety(terminates)]
fn f2() {
    f3();
}

#[safety(terminates)]
fn f3() {
    m::f1();
}
