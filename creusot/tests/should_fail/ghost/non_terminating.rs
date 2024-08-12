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

pub fn looping() {
    let _g: GhostBox<i32> = ghost! {
        loop {}
    };
}
