// Checks that unions don't cause a crash

extern crate creusot_contracts;

pub union DummyUnion {
    _field1: usize,
    _field2: isize,
}

pub fn x(_: DummyUnion) {}
