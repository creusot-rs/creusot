//! Definitions for pearlite code
//!
//! This contains types and traits that are meant to be used in logical code.

#![cfg_attr(not(creusot), allow(unused_imports))]
use crate::prelude::*;

pub mod fmap;
mod fset;
mod id;
mod int;
mod mapping;
pub mod ops;
pub mod ord;
pub mod ra;
pub mod real;
pub mod seq;
mod set;
mod well_founded;

pub use self::{
    fmap::FMap,
    fset::FSet,
    id::Id,
    int::{Int, Nat, Positive},
    mapping::Mapping,
    ord::OrdLogic,
    seq::Seq,
    set::Set,
    well_founded::WellFounded,
};

/// Creates a logical value satisfying the property given by `p`.
///
/// This is also called the "epsilon operator": its goal is not extract from `∃x. P(x)`
/// a `x` satisfying `P`.
#[trusted]
#[logic(opaque)]
#[requires(exists<x: T> p[x])]
#[ensures(p[result])]
pub fn such_that<T>(p: Mapping<T, bool>) -> T {
    dead
}

/// A variant of `such_that` that returns an `Option<T>`, returning `None` if no value satisfies
/// the property.
#[logic]
#[ensures(match result {
    Some(v) => p[v],
    None => forall<x: T> !p[x],
})]
pub fn try_such_that<T>(p: Mapping<T, bool>) -> Option<T> {
    pearlite! {
        if exists<x: T> p[x] {
            Some(such_that(p))
        } else {
            None
        }
    }
}

/// Return a logical value of type `T` without any constraints.
#[logic]
pub fn any<T>() -> T {
    such_that(|_| true)
}
