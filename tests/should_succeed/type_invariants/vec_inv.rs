extern crate creusot_std;
use creusot_std::{invariant::Invariant, prelude::*};

pub struct SumTo10 {
    pub a: i32,
    pub b: i32,
}

impl Invariant for SumTo10 {
    #[logic(open)]
    fn invariant(self) -> bool {
        pearlite! { self.a@ + self.b@ == 10 }
    }
}

#[requires(x@.len() > 0)]
pub fn vec(x: Vec<&mut SumTo10>) {
    proof_assert! { x[0].a@ + x[0].b@ == 10 };
}
