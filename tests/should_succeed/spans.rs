// CREUSOT_ARG=--span-mode=relative
// Test case for checking emitted spans
extern crate creusot_contracts;
use creusot_contracts::prelude::*;

pub trait Tr {
    #[requires(x)]
    #[ensures(result)]
    fn foo(x: bool) -> bool;
}

pub struct S;

impl Tr for S {
    #[requires(x && x)]
    #[ensures(result || result)]
    fn foo(x: bool) -> bool {
        x
    }
}

#[check(ghost)]
#[requires(i@ <= 0)]
pub fn bar(mut i: usize) -> usize {
    #[variant(i@)]
    #[invariant(i@ <= 0)]
    while 0 < i {
        i -= 1;
    }
    i
}

#[logic]
#[variant(i)]
#[requires(0 <= i)]
#[ensures(result == 0)]
pub fn baz(i: Int) -> Int {
    pearlite! {
        if i <= 0 {
            i
        } else {
            baz(i - 1)
        }
    }
}

pub struct NonNeg(pub usize);

impl Invariant for NonNeg {
    #[logic(open)]
    fn invariant(self) -> bool {
        pearlite! { 0 <= self.0@ }
    }
}

impl NonNeg {
    #[check(ghost)]
    #[requires(0 < self.0@)]
    #[ensures(result.0@ == self.0@ - 1)]
    pub fn decr(self) -> Self {
        Self(self.0 - 1)
    }
}

#[check(ghost)]
#[variant(i.0@)]
#[requires(0 <= i.0@)]
pub fn quux(i: NonNeg) -> NonNeg {
    if i.0 == 0 { i } else { quux(i.decr()) }
}
