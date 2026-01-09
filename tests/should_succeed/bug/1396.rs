extern crate creusot_std;
use creusot_std::prelude::*;

#[requires(f.precondition(()))]
#[ensures(f.postcondition_once((), ()))]
pub fn apply_once<F: FnOnce()>(f: F) {
    f()
}

#[requires(f.precondition(()))]
#[ensures(exists<g: F> f.postcondition_mut((), g, ()) && resolve(g))]
fn apply_mut<F: FnMut()>(mut f: F) {
    f()
}

pub fn foo1() {
    let mut x = 13;
    let r = &mut x;
    let snap_r = snapshot! { r };
    #[invariant((*r)@ == 13 + produced.len())]
    #[invariant(^*snap_r == ^r)]
    for _ in 0..42 - 13 {
        // BEGIN loop body
        apply_mut(
            #[requires((*r)@ < 42)]
            #[ensures((old(*r))@ + 1 == (*r)@)]
            || *r += 1,
        );
        // END loop body
    }
    proof_assert!(x@ == 42);
}

pub fn foo2() {
    let mut x = 13;
    let r = &mut x;
    let snap_r = snapshot! { r };
    #[invariant((*r)@ == 13 + produced.len())]
    #[invariant(^*snap_r == ^r)]
    for _ in 0..42 - 13 {
        // BEGIN loop body
        apply_mut(
            #[requires((*r)@ < 42)]
            #[ensures((*old(r))@ + 1 == (*r)@)]
            #[ensures(^old(r) == ^r)]
            || *r += 1,
        );
        // END loop body
    }
    proof_assert!(x@ == 42);
}

pub fn foo3() {
    let mut x = 13;
    let r = &mut x;
    let snap_r = snapshot! { r };
    #[invariant((*r)@ == 13 + produced.len())]
    #[invariant(^*snap_r == ^r)]
    for _ in 0..42 - 13 {
        // BEGIN loop body
        apply_mut(|| *r += 1);
        // END loop body
    }
    proof_assert!(x@ == 42);
}

pub fn foo4() {
    let mut x = 13;
    let r = &mut x;
    let snap_r = snapshot! { r };
    #[invariant((*r)@ == 13 + produced.len())]
    #[invariant(^*snap_r == ^r)]
    for _ in 0..42 - 13 {
        // BEGIN loop body
        apply_once(
            #[requires((*r)@ < 42)]
            #[ensures((old(*r))@ + 1 == (*r)@)]
            || *r += 1,
        );
        // END loop body
    }
    proof_assert!(x@ == 42);
}

pub fn foo5() {
    let mut x = 13;
    let r = &mut x;
    let snap_r = snapshot! { r };
    #[invariant((*r)@ == 13 + produced.len())]
    #[invariant(^*snap_r == ^r)]
    for _ in 0..42 - 13 {
        // BEGIN loop body
        apply_once(
            #[requires((*r)@ < 42)]
            #[ensures((old(*r))@ + 1 == (*r)@)]
            || *r += 1,
        );
        // END loop body
    }
    proof_assert!(x@ == 42);
}
