extern crate creusot_contracts;
use creusot_contracts::prusti_prelude::*;

trait Trait {}

impl<T> Trait for T {}

pub struct Wrap<T: Trait>(T);

#[open]
#[logic('x where 'curr: 'x)]
pub fn test_constructor<'x>(x: Box<u32>) -> Wrap<Box<u32>> {
    Wrap(at_expiry::<'x>(x))
}