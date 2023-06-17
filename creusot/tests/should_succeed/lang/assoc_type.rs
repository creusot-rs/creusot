extern crate creusot_contracts;

pub trait Tr {
    type A;
}

pub struct Assoc<T: Tr> {
    pub item: T::A,
}

pub fn uses<T: Tr>(_: Assoc<T>) {}

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

pub fn uses2<T: Tr>(_: Nested<T>) {}

pub struct Nested2 {
    pub item: Assoc<()>,
}

pub fn uses3(_: Nested2) {}
