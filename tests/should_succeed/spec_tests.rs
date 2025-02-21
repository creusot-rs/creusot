// NO_REPLAY

extern crate creusot_contracts;
use creusot_contracts::*;

enum T {
    A,
    B,
}

struct S<A, B>(A, B);

pub enum List<A> {
    Cons(A, Box<List<A>>),
    Nil,
}

#[ensures(T::A == T::B)]
#[ensures(S(0u32, true) == S(1u32, false))]
pub fn test_specs() {}
