extern crate creusot_contracts;
use creusot_contracts::{logic::Seq, *};

pub fn ghost_arg(g: Snapshot<u32>) {
    let _x: Snapshot<u32> = snapshot! { *g };
}

pub fn ghost_vec() {
    let x: Vec<u32> = Vec::new();
    let mut _s: Snapshot<Vec<_>> = snapshot! { x };
}

#[open]
#[logic]
pub fn omg() {}

pub fn ghost_copy() {
    let a = 0;
    let mut _s = snapshot! { Seq::empty().push_back(0i32) };
    _s = snapshot! { _s.push_back(a) };
}

pub fn ghost_is_copy() {
    let mut x = 0;
    let r = &mut x;
    let g = snapshot! { r };
    let g1 = g;
    let g2 = g;
    proof_assert!(g1 == g2);
}

#[logic]
fn logi_drop<T>(_: T) {}

pub fn ghost_check() {
    let mut x = Vec::new();

    // We ghost capture the value and then drop it without affecting program
    snapshot! { logi_drop(x); };

    x.push(0);

    assert!(x.len() == 1);
}

pub struct MyStruct {
    f: u32,
    g: Snapshot<u32>,
}

#[requires(x.g@ == 0)]
pub fn takes_struct(mut x: MyStruct) {
    x.g = snapshot! { x.f };
}
