extern crate creusot_contracts;

use creusot_contracts::*;

// Ensure that different kinds of functions are translated to the
// correct abstract symbol in Rust
pub trait Tr {
    #[logic]
    fn logical(&self) -> Int;
    #[predicate]
    fn predicate(&self) -> bool;
    fn program(&self) {}
}

pub fn test<T: Tr>(_: T) {}
