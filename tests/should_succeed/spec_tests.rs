// NO_REPLAY

extern crate creusot_contracts;
use creusot_contracts::*;

pub enum T {
    A,
    B,
}

pub struct S<A, B>(pub A, pub B);

pub enum List<A> {
    Cons(A, Box<List<A>>),
    Nil,
}

#[ensures(T::A == T::B)]
#[ensures(S(0u32, true) == S(1u32, false))]
pub fn test_specs() {}
