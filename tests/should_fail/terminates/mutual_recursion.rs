#![allow(unused)]
extern crate creusot_std;
use creusot_std::prelude::*;

mod m {
    #[super::check(terminates)]
    pub fn f1() {
        super::f2();
    }
}

#[check(terminates)]
fn f2() {
    f3();
}

#[check(terminates)]
fn f3() {
    m::f1();
}
