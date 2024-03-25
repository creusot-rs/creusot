extern crate creusot_contracts;
use creusot_contracts::prusti_prelude::{self, *};

struct Test<'a, X, Y>(&'a X, Y);

impl<'a, X, Y: Copy> prusti_prelude::Clone for Test<'a, X, Y> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<'a, X, Y: Copy> Copy for Test<'a, X, Y> {}
#[ensures(x == x)]
fn test(x: Test<'_, Box<u32>, Box<u32>>) {}
