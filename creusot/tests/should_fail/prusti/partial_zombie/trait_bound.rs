extern crate creusot_contracts;
use creusot_contracts::prusti_prelude::{self, *};

pub trait Trait {}

impl Trait for Box<u32> {}

enum MyOp<X: Trait> {
    None,
    Some(X),
}

impl<X: Copy + Trait> prusti_prelude::Clone for MyOp<X> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<X: Copy + Trait> Copy for MyOp<X> {}

#[ensures(x == x)]
fn test(x: MyOp<Box<u32>>) {}
