// WHY3PROVE SHOULD_PROVE Z3 NO_SPLIT
extern crate creusot_std;
use creusot_std::{logic::Int, prelude::*};

pub trait A {
    #[logic]
    fn mktrue() -> Int {
        pearlite! { 5 }
    }

    // Should not be provable
    #[logic(law)]
    #[ensures(Self::mktrue() <= 10)]
    fn is_true() {
        ()
    }
}

impl A for () {
    #[logic]
    fn mktrue() -> Int {
        pearlite! { 6 }
    }
}

// Check that we can still see the bodies of default implementations which are marked as final though.
pub trait Invariant {
    #[logic]
    fn invariant(self) -> bool {
        true
    }
}

pub struct Once<T>(Option<T>);

impl<T> Invariant for Once<T> {}

#[requires(x.invariant())]
#[ensures((^x).invariant())]
pub fn uses_invariant<T>(x: &mut Once<T>) {
    x.0.take();
}
