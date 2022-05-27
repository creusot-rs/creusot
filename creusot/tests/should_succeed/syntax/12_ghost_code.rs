extern crate creusot_contracts;
use creusot_contracts::*;

pub fn ghost_arg(g: Ghost<u32>) {
    let _x: Ghost<u32> = ghost! { *g };
}

pub fn ghost_vec() {
    let x: Vec<u32> = Vec::new();
    let mut _s: Ghost<Vec<_>> = ghost! { x };
}

#[logic]
fn omg() {}

pub fn ghost_copy() {
    let a = 0;
    let mut _s = ghost! { Seq::EMPTY.push(0) };
    _s = ghost! { { _s.push(a) } };
}

#[logic]
fn logi_drop<T>(_: T) {}

pub fn ghost_check() {
    let mut x = Vec::new();

    // We ghost capture the value and then drop it without affecting program
    ghost! { {logi_drop(x); } };

    x.push(0);

    assert!(x.len() == 1);
}
