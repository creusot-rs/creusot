extern crate creusot_contracts;
use creusot_contracts::*;

#[check(ghost)]
pub fn recursive() {
    ghost! {
        f();
        42
    };
}

#[check(ghost)]
fn f() {
    recursive();
}

#[allow(unreachable_code)]
pub fn looping() {
    let _g: Ghost<i32> = ghost! {
        loop {}
    };
}
