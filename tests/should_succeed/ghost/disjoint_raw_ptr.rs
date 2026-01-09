extern crate creusot_std;
use creusot_std::{ghost::perm::Perm, prelude::*};

pub fn foo() {
    let (p1, mut own1) = Perm::new(1i32);
    let (p2, own2) = Perm::new(1i32);

    ghost! {
        let _ = Perm::disjoint_lemma(&mut own1, &own2);
    };
    proof_assert!(own1 != own2);
    proof_assert!(p1 != p2);
}
