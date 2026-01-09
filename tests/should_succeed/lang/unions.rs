// Checks that unions don't cause a crash
// FIXME: this is unsound, of course.

extern crate creusot_std;

pub union DummyUnion {
    _field1: usize,
    _field2: isize,
}

pub fn x(_: DummyUnion) {}
