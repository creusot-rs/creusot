#![cfg_attr(not(creusot), allow(unused_imports))]

mod fmap;
mod fset;
mod int;
mod mapping;
mod ops;
pub mod ord;
#[cfg(feature = "why3_seq")]
mod seq;

#[cfg(not(feature = "why3_seq"))]
mod seq2;
#[cfg(not(feature = "why3_seq"))]
use seq2 as seq;
mod set;

pub use fmap::FMap;
pub use fset::FSet;
pub use int::Int;
pub use mapping::Mapping;
pub use ops::IndexLogic;
pub use ord::OrdLogic;
pub use seq::Seq;
pub use set::Set;
