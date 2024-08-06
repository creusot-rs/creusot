#![cfg_attr(not(creusot), allow(unused_imports))]

mod fmap;
mod fset;
mod int;
mod mapping;
mod ops;
pub mod ord;
#[cfg(feature = "why3_seq")]
mod seq;

#[cfg(all(not(feature = "why3_seq"), not(feature = "extensional_seq")))]
mod seq2;
#[cfg(all(not(feature = "why3_seq"), not(feature = "extensional_seq")))]
use seq2 as seq;
#[cfg(all(not(feature = "why3_seq"), feature = "extensional_seq"))]
mod seq3;
#[cfg(all(not(feature = "why3_seq"), feature = "extensional_seq"))]
use seq3 as seq;
mod set;

pub use fmap::FMap;
pub use fset::FSet;
pub use int::Int;
pub use mapping::Mapping;
pub use ops::IndexLogic;
pub use ord::OrdLogic;
pub use seq::Seq;
pub use set::Set;
