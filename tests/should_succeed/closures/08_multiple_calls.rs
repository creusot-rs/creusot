extern crate creusot_std;
use creusot_std::prelude::*;

pub fn multi_use<T>(x: &T) {
    let c = #[requires(x == x)]
    || {
        let _ = x;
        0
    };

    uses_fn(c);
    // uses_fnmut(c);
    // uses_fnonce(c);
}

#[trusted]
#[requires(f.precondition(()))]
#[ensures(exists<f2: &F, r> *f2 == f && f2.postcondition((), r))]
fn uses_fn<F: Fn() -> u32>(f: F) {
    f();
}

// #[requires(f.precondition(()))]
// #[ensures(exists<f2: F, r> f2.postcondition_mut((), f2, r))]
// fn uses_fnmut<F: FnMut() -> u32>(mut f: F) {
//     f();
// }

// #[requires(f.precondition(()))]
// #[ensures(exists<r> f.postcondition_once((), r))]
// fn uses_fnonce<F: FnOnce() -> u32>(f: F) {
//     f();
// }
