// WHY3PROVE
extern crate creusot_contracts;
use creusot_contracts::{vec, *};

pub fn test() {
    let mut v = vec![1, 2, 2, 3];
    v.dedup();
    proof_assert! { v@.len() == 3 };
}

struct S(u32);
impl Invariant for S {
    #[logic(prophetic)]
    #[open(self)]
    fn invariant(self) -> bool {
        self.0 == 0u32
    }
}

pub fn test2() {
    let v = vec![S(0)];
    let b = !v.is_empty();
    proof_assert! { b };
}

pub fn test3() {
    let v = vec![S(0)];
    proof_assert! { v@[0].0 == 0u32 };
}
