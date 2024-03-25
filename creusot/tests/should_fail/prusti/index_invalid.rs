extern crate creusot_contracts;
use creusot_contracts::prusti_prelude::*;

#[requires((*v)@.len() > 0)]
#[ensures(*result == old(*v)@[0])]
pub fn first<T>(v: &mut Vec<T>) -> &mut T {
    &mut v[0]
}
