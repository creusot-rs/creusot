extern crate creusot_contracts;
use creusot_contracts::prusti_prelude::*;

#[logic(('x) -> 'x)]
pub fn deref1<'a, T>(x: Box<&'a T>) -> &'a T {
    *x
}

#[logic(('x) -> 'curr)]
pub fn deref2<'a, T>(x: &'a Box<&'a Box<T>>) -> Box<T> {
    ***x
}

#[trusted]
#[logic(() -> '_)]
pub fn deref3<T>() -> Box<T> {
    absurd
}