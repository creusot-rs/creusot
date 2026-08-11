extern crate creusot_std;
use creusot_std::prelude::*;

pub enum E {
    A(u32),
}

/// A tuple-variant constructor used as a function value. The postcondition is only provable if the
/// constructor carries its meaning — `result = A x` — rather than an opaque one.
#[ensures(forall<x: u32> o == Some(x) ==> result == Some(E::A(x)))]
#[ensures(o == None ==> result == None)]
pub fn g(o: Option<u32>) -> Option<E> {
    o.map(E::A)
}
