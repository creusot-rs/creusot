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

/// A constructor from another crate. It needs no written spec, so it must not be poisoned the way
/// an unspecified extern function is.
#[ensures(result == o.map_logic(|x| Some(x)))]
pub fn g_extern<A>(o: Option<A>) -> Option<Option<A>> {
    o.map(Some)
}

pub struct T0();

/// Zero arity.
#[ensures(result == T0())]
pub fn h() -> T0 {
    let t = T0;
    t()
}

#[allow(dead_code)]
pub struct T2(u32, u32);

/// More than one argument, so the fields must stay in order.
#[ensures(result == T2(0u32, 1u32))]
pub fn i() -> T2 {
    let t = T2;
    t(0, 1)
}
