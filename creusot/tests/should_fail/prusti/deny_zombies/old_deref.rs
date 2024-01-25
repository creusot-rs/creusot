#![deny(creusot::prusti_zombie)]
extern crate creusot_contracts;
use creusot_contracts::prusti_prelude::*;

#[ensures(*old(x) == *result)]
pub fn zombie_old<T>(x: Box<T>) -> Box<T> {
    x
}
