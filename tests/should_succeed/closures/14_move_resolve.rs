extern crate creusot_std;
use creusot_std::{mode::Mode, prelude::*};

#[allow(unused_must_use)]
pub fn f<T>(x: T) {
    let xx = snapshot!(x);
    let f = #[requires(true)]
    move || {
        &x;
    };
    proof_assert!(forall<mode: Mode> f.postcondition_once(mode, (), ()) ==> resolve(*xx));
    f()
}

#[allow(unused_must_use)]
pub fn g<T>(x: T) {
    let xx = snapshot!(x);
    let f = move || {
        &x;
    };
    proof_assert!(forall<mode: Mode> f.postcondition_once(mode, (), ()) ==> resolve(*xx));
    f()
}
