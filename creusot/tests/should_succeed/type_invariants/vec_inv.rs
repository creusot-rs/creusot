extern crate creusot_contracts;
use creusot_contracts::{invariant::Invariant, *};

pub struct SumTo10 {
    a: i32,
    b: i32,
}

impl Invariant for SumTo10 {
    #[open]
    #[predicate]
    fn invariant(self) -> bool {
        pearlite! { self.a@ + self.b@ == 10 }
    }
}

#[requires(x@.len() > 0)]
pub fn vec(x: Vec<&mut SumTo10>) {
    proof_assert! { x[0].a@ + x[0].b@ == 10 };
}
