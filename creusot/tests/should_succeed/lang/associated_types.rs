extern crate creusot_contracts;

pub trait Tr {
    type A;
}

pub struct Assoc<T: Tr> {
    item: T::A,
}

pub fn uses<T: Tr>(_: Assoc<T>) {}


impl Tr for () {
    type A = bool;
}

pub fn uses_instance(x: Assoc<()>) -> bool {
    x.item
}