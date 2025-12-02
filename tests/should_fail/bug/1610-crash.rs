// Test a crash when trying to implement collect
// This test may become should_succeed in the future.
extern crate creusot_contracts;
use creusot_contracts::prelude::*;

struct P();

impl ::std::iter::Iterator for P {
    type Item = ();
    fn next(&mut self) -> Option<Self::Item> {
        None
    }

    fn collect<B: FromIterator<Self::Item>>(self) -> B {
        std::iter::empty().collect()
    }
}
