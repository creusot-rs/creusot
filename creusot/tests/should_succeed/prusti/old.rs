#![warn(creusot::prusti_final)]
#![deny(creusot::prusti_zombie)]
extern crate creusot_contracts;
use creusot_contracts::prusti_prelude::*;

#[ensures(0u32 == at::<'pre>(*x))]
pub fn test<'pre>(x: Box<u32>) {}
