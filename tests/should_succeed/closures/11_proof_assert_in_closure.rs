extern crate creusot_std;
use creusot_std::prelude::*;

pub fn immutable_capture() {
    let x = 1;
    (#[requires(x == 1i32)]
    || {
        proof_assert!(x == 1i32);
    })();
}

pub fn mutable_capture() {
    let mut x = 1;
    (#[requires(x == 1i32)]
    || {
        proof_assert!(x == 1i32);
        x = 2;
        proof_assert!(x == 2i32);
    })();
}

#[trusted]
#[requires(f.precondition(()))]
#[ensures(f.postcondition_once((), ()))]
fn calls_closure<F: FnOnce() -> ()>(f: F) {
    f();
}

pub fn captures_and_call() {
    let mut x = 1;
    let clos = #[requires(x == 1i32)]
    #[ensures(x == 2i32)]
    || {
        proof_assert!(x == 1i32);
        x = 2;
        proof_assert!(x == 2i32);
    };
    calls_closure(clos);
    proof_assert!(x == 2i32);
}
