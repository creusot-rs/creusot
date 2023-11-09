extern crate creusot_contracts;
use creusot_contracts::*;

pub trait Tr {
    type A;
}

pub struct Assoc<U: Tr> {
    pub item: U::A,
}

pub fn uses<A: Tr>(_: Assoc<A>) {}

pub struct Assoc2<U: Tr, F, B> {
    pub x: F,
    pub item: U::A,
    pub y: B,
}

pub fn uses2<C: Tr, X, Y>(_: Assoc2<C, X, Y>) {}

impl Tr for () {
    type A = usize;
}

pub struct Fix {
    pub item: <() as Tr>::A,
}

pub fn mono(_: Fix) {}

pub struct Nested<T: Tr> {
    pub item: Assoc<T>,
}

pub fn uses3<T: Tr>(_: Nested<T>) {}

pub struct Nested2 {
    pub item: Assoc<()>,
}

pub fn uses4(_: Nested2) {}

pub struct Map<I: Tr> {
    pub iter: I,
    pub produced: Ghost<Seq<I::A>>,
}

pub fn use_map<I: Tr>(_: Map<I>) {}
