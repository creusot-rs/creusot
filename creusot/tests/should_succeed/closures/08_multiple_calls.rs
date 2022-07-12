extern crate creusot_contracts;
use creusot_contracts::{std::*, *};

pub fn multi_use<T>(x: &T) {
    let c = #[requires(x == x)]
    || {
        let _ = x;
        0
    };

    uses_fn(c);
    uses_fnmut(c);
    uses_fnonce(c);
}

#[trusted]
#[requires(f.precondition(()))]
#[ensures(exists<f2 : &F, r : _> *f2 == f && f2.postcondition((), r))]
fn uses_fn<F: Fn() -> u32>(f: F) {
    f();
}

#[requires(f.precondition(()))]
#[ensures(exists<f2 : &mut F, r : _> *f2 == f && f2.postcondition_mut((), r))]
fn uses_fnmut<F: FnMut() -> u32>(mut f: F) {
    f();
}

#[requires(f.precondition(()))]
#[ensures(exists<r : _> f.postcondition_once((), r))]
fn uses_fnonce<F: FnOnce() -> u32>(f: F) {
    f();
}
