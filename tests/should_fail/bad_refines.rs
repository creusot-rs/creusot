extern crate creusot_contracts;
use creusot_contracts::*;

pub fn baz<const N: i32>() -> i32 {
    N
}

#[refines(baz::<N>)]
pub fn baz2<const N: i32>() -> i32 {
    N
}

pub fn bar(x: i32) -> i32 {
    baz::<42>()
}

#[refines(bar)]
pub fn bar2(x: i32) -> i32 {
    baz::<42>() // TODO 0
}

#[refines(bar)]
pub fn bar3(x: i32) -> i32 {
    baz2::<0>()
}
