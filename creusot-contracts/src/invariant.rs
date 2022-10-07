#[cfg(feature = "contracts")]
use crate as creusot_contracts;

use crate::macros::*;

pub trait Invariant {
    #[predicate]
    fn invariant(self) -> bool;
}
