//! Definitions for pearlite code
//!
//! This contains types and traits that are meant to be used in logical code.

#![cfg_attr(not(creusot), allow(unused_imports))]

mod fmap;
pub mod fset;
mod id;
mod int;
mod mapping;
pub mod ops;
pub mod ord;
pub mod ra;
pub mod seq;
mod set;

pub use self::{
    fmap::FMap, fset::FSet, id::Id, int::Int, mapping::Mapping, ord::OrdLogic, seq::Seq, set::Set,
};
