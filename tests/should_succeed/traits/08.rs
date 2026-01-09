extern crate creusot_std;

use creusot_std::{logic::Int, prelude::*};

// Ensure that different kinds of functions are translated to the
// correct abstract symbol in Rust
pub trait Tr {
    #[logic]
    fn logical(&self) -> Int;
    fn program(&self) {}
}

pub fn test<T: Tr>(_: T) {}
