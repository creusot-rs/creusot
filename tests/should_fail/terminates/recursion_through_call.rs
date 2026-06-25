#![feature(fn_traits)]

extern crate creusot_std;
use creusot_std::prelude::*;

#[check(terminates)]
pub fn f() {
    g();
}

#[check(terminates)]
pub fn g() {
    let fp: fn() = f;
    fp.call(());
}
