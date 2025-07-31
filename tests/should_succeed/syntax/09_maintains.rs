#![allow(unused_variables)]

extern crate creusot_contracts;
use creusot_contracts::{logic::Int, *};

// Tests that we can use field access syntax in pearlite.

pub struct A {}

impl A {
    #[logic]
    pub fn invariant(self, b: bool, c: u64) -> bool {
        true
    }

    #[logic]
    pub fn inv2(self, b: Int) -> bool {
        true
    }
}

#[logic]
pub fn other_inv(a: A, b: bool) -> bool {
    true
}

#[maintains(a.invariant(b, c))]
pub fn test_1(a: A, b: bool, c: u64) {}

#[maintains((mut a).invariant(b, c))]
pub fn test_2(a: &mut A, b: bool, c: u64) {}

#[maintains((mut a).invariant(mut b, c))]
pub fn test_3(a: &mut A, b: &mut bool, c: u64) {}

#[maintains(a.inv2(b@ + 0))]
pub fn test_5(a: A, b: usize) {}

#[maintains(other_inv(a, b))]
pub fn test_6(a: A, b: bool) {}
