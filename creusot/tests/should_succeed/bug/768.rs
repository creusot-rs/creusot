extern crate creusot_contracts;
use creusot_contracts::*;

pub struct A {
    pub l: usize,
    pub r: usize,
}

impl A {
    #[open]
    #[logic]
    pub fn with_l(self, l: usize) -> Self {
        A { l, ..self }
    }
}
