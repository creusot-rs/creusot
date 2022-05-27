extern crate creusot_contracts;
use creusot_contracts::*;

fn ghost_arg(g: Ghost<u32>) {
    let x: Ghost<u32> = ghost! { *g };
}

fn ghost_vec() {
    let x: Vec<u32> = Vec::new();
    let mut s: Ghost<Vec<_>> = ghost! { x };
}

#[logic]
fn omg() {}

fn ghost_copy() {
    let a = 0;
    let mut s = ghost! { Seq::EMPTY.push(0) };
    s = ghost! { { s.push(a) } };
}

#[logic]
fn logi_drop<T>(_: T) {}

fn ghost_check() {
    let mut x = Vec::new();

    // We ghost capture the value and then drop it without affecting program
    ghost! { {logi_drop(x); } };

    x.push(0);

    assert!(x.len() == 1);
}
