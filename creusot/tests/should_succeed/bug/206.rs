extern crate creusot_contracts;

use creusot_contracts::std::*;
use creusot_contracts::*;

struct A(Vec<usize>);
#[logic]
#[ensures(@a.0 === @a.0)]
fn u2(a: A) {}

#[logic]
fn u(a: A) {
    pearlite! {
        u2(a)
    }
}

#[ensures(u(*a) === (u(*a)))]
fn ex(a: &A) {}
