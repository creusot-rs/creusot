extern crate creusot_contracts;
use creusot_contracts::prusti_prelude::{self, *};

struct Test<X>(X);

impl prusti_prelude::Clone for Test<u32> {
    fn clone(&self) -> Self {
        *self
    }
}

impl prusti_prelude::Clone for Test<bool> {
    fn clone(&self) -> Self {
        *self
    }
}

impl Copy for Test<u32> {}
impl Copy for Test<bool> {}
#[ensures(x == x)]
fn test(x: (Test<Box<u32>>, Test<u32>)) {}
