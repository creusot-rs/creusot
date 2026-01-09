// WHY3PROVE
extern crate creusot_std;
use creusot_std::{
    ghost::perm::Perm,
    prelude::{vec, *},
};

pub fn zst_pointers_may_be_equal() {
    let mut v0: Vec<()> = vec![()];
    let v1: Vec<()> = vec![()];
    let (p1, own1) = Perm::from_mut(&mut v0[0]);
    let (p2, own2) = Perm::from_ref(&v1[0]);
    ghost! { Perm::disjoint_lemma(own1.into_inner(), own2.into_inner()) };
    // This is actually false because p1 and p2 are both equal to NonNull::dangling()
    // The fix was to add a precondition to disjoint_lemma that the pointee size should be non-zero
    proof_assert! { p1.addr_logic() != p2.addr_logic() }
}
