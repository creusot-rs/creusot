#![allow(unused)]
extern crate creusot_std;
use creusot_std::prelude::*;

pub trait P {
    type A;
}

pub struct S<T: P<A: P>>(pub T::A);

pub struct Bad(Box<S<Sneaky>>);

impl P for Bad {
    type A = Bad;
}

pub struct Sneaky;

impl P for Sneaky {
    type A = Bad;
}
