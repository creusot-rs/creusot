//! Definitions for pearlite code
//!
//! This contains types and traits that are meant to be used in logical code.

#![cfg_attr(not(creusot), allow(unused_imports))]
use crate::*;

mod fmap;
pub mod fset;
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
    fmap::FMap, fset::FSet, id::Id, int::Int, mapping::Mapping, ord::OrdLogic, seq::Seq, set::Set,
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
pub fn such_that<T>(p: crate::logic::Mapping<T, bool>) -> T {
    dead
}

/// Indicates unreachable code in logic.
///
/// This function indicates a logical branch that should be impossible to reach.
#[trusted]
#[logic(opaque)]
#[requires(false)]
#[ensures(false)]
#[variant(0)]
#[allow(unconditional_recursion)]
pub fn unreachable<T>() -> T {
    unreachable()
}
