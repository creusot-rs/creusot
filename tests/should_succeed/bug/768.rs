extern crate creusot_std;
use creusot_std::prelude::*;

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
