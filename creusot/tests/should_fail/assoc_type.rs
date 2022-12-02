extern crate creusot_contracts;
use creusot_contracts::*;

trait Tr {
    type A;
}

struct Assoc<T: Tr> {
    item: T::A,
}

fn uses<T: Tr>(x: Assoc<T>) {}
