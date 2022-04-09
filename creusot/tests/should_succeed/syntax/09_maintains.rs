extern crate creusot_contracts;

use creusot_contracts::*;

// Tests that we can use field access syntax in pearlite.

struct A {}

impl A {
    #[predicate]
    fn invariant(self, b: bool, c: u64) -> bool {
        true
    }

    #[predicate]
    fn inv2(self, b: Int) -> bool {
        true
    }
}

#[predicate]
fn other_inv(a: A, b: bool) -> bool {
    true
}

#[maintains(a.invariant(b, c))]
fn test_1(a: A, b: bool, c: u64) {}

#[maintains((mut a).invariant(b, c))]
fn test_2(a: &mut A, b: bool, c: u64) {}

#[maintains((mut a).invariant(mut b, c))]
fn test_3(a: &mut A, b: &mut bool, c: u64) {}

#[maintains(a.inv2(@b + 0))]
fn test_5(a: A, b: usize) {}

#[maintains(other_inv(a, b))]
fn test_6(a: A, b: bool) {}
