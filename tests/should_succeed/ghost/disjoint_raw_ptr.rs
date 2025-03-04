extern crate creusot_contracts;
use creusot_contracts::{ptr_own::PtrOwn, *};

pub fn foo() {
    let (p1, mut own1) = PtrOwn::new(1i32);
    let (p2, own2) = PtrOwn::new(1i32);

    ghost! {
        let _ = PtrOwn::disjoint_lemma(&mut own1, &own2);
    };
    proof_assert!(own1 != own2);
    proof_assert!(p1 != p2);
}
