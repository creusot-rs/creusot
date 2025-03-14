extern crate creusot_contracts;
use creusot_contracts::*;

#[pure]
pub fn recursive() {
    ghost! {
        f();
        42
    };
}

#[pure]
fn f() {
    recursive();
}

#[allow(unreachable_code)]
pub fn looping() {
    let _g: Ghost<i32> = ghost! {
        loop {}
    };
}
