// WHY3PROVE
extern crate creusot_contracts;
use creusot_contracts::*;

// Since we reborrow `bor` after `b1`, its prophecy depends on `b2` and not `b1`
pub fn not_final_borrow<T: Copy>(bor: &mut T) {
    let b1 = &mut *bor;
    let _b2 = &mut *bor;
    proof_assert!(b1 == bor);
}

pub fn store_changes_prophecy<T: Copy>(bor: &mut T) {
    let b1 = &mut *bor;
    let val = *b1;
    // The prophecy of `bor` changed here after the reborrow
    *bor = val;
    proof_assert!(b1 == bor);
}

pub fn store_changes_prophecy_2<T: Copy>(bor: &mut T, x: T) {
    let b1 = &mut *bor;
    *b1 = x;
    // The prophecy of `bor` changed here after the reborrow
    *bor = x;
    proof_assert!(b1 == bor);
}

pub fn call_changes_prophecy(bor: &mut i32) {
    #[trusted]
    #[ensures(result@ == 2)]
    fn inner() -> i32 {
        2
    }
    let bor_snap = snapshot!(bor);
    let b1 = &mut *bor;
    let b1_snap = snapshot!(b1);
    *b1 = inner();
    // The prophecy of `bor` changed here after the reborrow
    *bor = inner();
    proof_assert!(*b1_snap == *bor_snap);
}

pub fn unnesting_fails() {
    let mut x = 0;
    let mut bor = &mut x;
    let nested = &mut bor;
    // When unnesting, we can't statically track the prophecy in the inner borrow
    let rebor1 = &mut **nested;
    let rebor2 = &mut **nested;
    proof_assert!(rebor1 == rebor2);
}

// `bor` is a place that does not contain a mutable deref, but it is moved after it has been reborrowed.
pub fn move_place_without_deref<T>(bor: Box<&mut T>) {
    #[trusted]
    #[ensures(**x == ^*x)]
    fn inner<T>(x: Box<&mut T>) {}
    let bor_snap = snapshot!(*bor);
    let b1 = &mut **bor;
    inner(bor);
    proof_assert!(*b1 == **bor_snap && ^b1 == ^*bor_snap); // Passes
    proof_assert!(b1 == *bor_snap); // Fails
}
