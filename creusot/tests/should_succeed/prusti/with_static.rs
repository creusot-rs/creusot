#![warn(creusot::prusti_final)]
extern crate creusot_contracts;
use creusot_contracts::prusti_prelude::*;

#[open]
#[logic]
pub fn id<X>(x: WithStatic<X>) -> WithStatic<X> {
    x
}

#[open]
#[logic]
pub fn id2<'a>(x: WithStatic<&'a u32>) -> &'static u32 {
    id::<&u32>(x)
}

#[open]
#[logic]
pub fn test<X>(x: WithStatic<(X, X)>) -> WithStatic<X> {
    x.0
}
