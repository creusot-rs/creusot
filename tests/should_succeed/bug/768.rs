extern crate creusot_contracts;
use creusot_contracts::*;

pub struct A {
    pub l: usize,
    pub r: usize,
}

impl A {
    #[logic(open)]
    pub fn with_l(self, l: usize) -> Self {
        A { l, ..self }
    }
}
