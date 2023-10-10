extern crate creusot_contracts;
use creusot_contracts::{logic::Seq, *};

pub fn ghost_arg(g: Ghost<u32>) {
    let _x: Ghost<u32> = gh! { *g };
}

pub fn ghost_vec() {
    let x: Vec<u32> = Vec::new();
    let mut _s: Ghost<Vec<_>> = gh! { x };
}

#[open]
#[ghost]
pub fn omg() {}

pub fn ghost_copy() {
    let a = 0;
    let mut _s = gh! { Seq::EMPTY.push(0i32) };
    _s = gh! { _s.push(a) };
}

pub fn ghost_is_copy() {
    let mut x = 0;
    let r = &mut x;
    let g = gh! { r };
    let g1 = g;
    let g2 = g;
    proof_assert!(g1 == g2);
}

#[ghost]
fn logi_drop<T>(_: T) {}

pub fn ghost_check() {
    let mut x = Vec::new();

    // We ghost capture the value and then drop it without affecting program
    gh! { logi_drop(x); };

    x.push(0);

    assert!(x.len() == 1);
}

pub struct MyStruct {
    f: u32,
    g: Ghost<u32>,
}

#[requires(x.g@ == 0)]
pub fn takes_struct(mut x: MyStruct) {
    x.g = gh! { x.f };
}
