#![allow(unused)]
extern crate creusot_contracts;
use creusot_contracts::*;

mod m {
    pub fn f1() {
        super::f2();
    }
}

fn f2() {
    f3();
}

fn f3() {
    m::f1();
}
