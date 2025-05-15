extern crate creusot_contracts;
use creusot_contracts::*;

#[allow(unused_must_use)]
pub fn f<T>(x: T) {
    let xx = snapshot!(x);
    let f = #[requires(true)]
    move || {
        &x;
    };
    proof_assert!(f.postcondition_once((), ()) ==> resolve(&*xx));
    f()
}

#[allow(unused_must_use)]
pub fn g<T>(x: T) {
    let xx = snapshot!(x);
    let f = move || {
        &x;
    };
    proof_assert!(f.postcondition_once((), ()) ==> resolve(&*xx));
    f()
}
