extern crate creusot_contracts;

use creusot_contracts::*;

fn x<T>(a: Option<T>) {
    match a {
        None => (),
        Some(x) => (),
    }
}

pub struct A(Vec<usize>);

#[logic]
#[ensures(@a.0 == @a.0)]
fn u2(a: A) {}

#[logic]
pub fn u(a: A) {
    pearlite! {
        u2(a)
    }
}

#[ensures(u(*a) == (u(*a)))]
pub fn ex(a: &A) {}
