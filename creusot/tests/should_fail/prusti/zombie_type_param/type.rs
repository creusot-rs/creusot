extern crate creusot_contracts;
use creusot_contracts::prusti_prelude::*;

pub trait Trait {}

impl Trait for Box<u32> {}
enum MyOp<X: Trait> {
    None,
    Some(X),
}

#[ensures(MyOp::Some(x) != MyOp::None)]
pub fn test_op(x: Box<u32>) {}
