// SHORT_ERROR
extern crate creusot_std;
use creusot_std::prelude::*;

#[logic]
#[ensures(false)]
#[allow(unconditional_recursion)]
pub fn falso() {
    falso()
}

pub trait Tr {
    #[logic]
    fn me(self);
}

impl<T> Tr for T {
    #[logic]
    #[allow(unconditional_recursion)]
    fn me(self) {
        self.me() // Make sure to resolve the instance to see the loop
    }
}

pub struct Never(Box<Never>);

#[logic]
#[allow(unconditional_recursion)]
pub fn sneak(n: Never) {
    match n {
        Never(m) => sneak(*m),
    }
    sneak(n) // the termination check once accepted if the argument decreased in at least one call
}

#[logic]
#[allow(unconditional_recursion)]
pub fn nonstrictly(i: usize) {
    match i {
        i => nonstrictly(i), // not strict subterm
    }
}

#[logic]
#[allow(unconditional_recursion)]
pub fn nested(n: Never, _: ()) {
    match n {
        Never(m) => nested(*m, nested(n, ())), // remember to check arguments of the recursive function!
    }
}
