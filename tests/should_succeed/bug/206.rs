extern crate creusot_contracts;

use creusot_contracts::*;

pub struct A(Vec<usize>);

#[logic]
#[ensures(a.0@ == a.0@)]
fn u2(a: A) {}

#[logic(open(self))]
pub fn u(a: A) {
    pearlite! {
        u2(a)
    }
}

#[ensures(u(*a) == (u(*a)))]
pub fn ex(a: &A) {}
