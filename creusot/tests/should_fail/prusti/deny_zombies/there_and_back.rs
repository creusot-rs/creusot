#![deny(creusot::prusti_zombie)]
extern crate creusot_contracts;
use creusot_contracts::prusti_prelude::*;

#[ensures({let y = x; *old(y) == 0u32})]
pub fn zombie_old(x: &u32) -> &u32  {
    x
}