#![allow(unused)]
extern crate creusot_contracts;
use creusot_contracts::*;

#[logic]
fn with_proof_assert(x: Int) {
    proof_assert! {
        x == f1()
    }
}

#[logic]
fn f1() -> Int {
    with_proof_assert(5);
    3
}

#[logic]
#[requires(x == f2())]
fn with_requires(x: Int) {}

#[logic]
fn f2() -> Int {
    with_requires(5);
    3
}