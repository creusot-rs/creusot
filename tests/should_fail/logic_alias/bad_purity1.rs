extern crate creusot_std;
use creusot_std::prelude::*;

#[logic(prophetic)]
fn zero_log() -> usize {
    0usize
}

#[logic_alias(zero_log)]
fn zero() -> usize {
    0
}

fn foo() {
    let _ = snapshot! { zero() };
}
