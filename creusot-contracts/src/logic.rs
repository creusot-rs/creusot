//! Definitions for pearlite code
//!
//! This contains types and traits that are meant to be used in logical code.

#![cfg_attr(not(creusot), allow(unused_imports))]

mod fmap;
pub mod fset;
mod int;
mod mapping;
pub mod ops;
pub mod ord;
mod seq;
mod set;

pub use fmap::FMap;
pub use fset::FSet;
pub use int::Int;
pub use mapping::Mapping;
pub use ord::OrdLogic;
pub use seq::Seq;
pub use set::Set;
