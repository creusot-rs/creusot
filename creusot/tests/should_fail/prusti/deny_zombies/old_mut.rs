#![deny(creusot::prusti_zombie)]
extern crate creusot_contracts;
use creusot_contracts::prusti_prelude::*;

#[ensures(*x.0 == *result)]
pub fn zombie_old<'a, T>(x: (&'a mut T, u32)) -> &'a mut T {
    x.0
}