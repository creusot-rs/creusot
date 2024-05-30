#![deny(creusot::prusti_zombie)]
extern crate creusot_contracts;
use creusot_contracts::prusti_prelude::*;

#[ensures(x.0 == x.0)]
#[ensures((old(x)).1 == result)]
pub fn zombie_old<T>(x: (T, u32)) -> u32 {
    x.1
}
