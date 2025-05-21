extern crate creusot_contracts;
use creusot_contracts::*;

pub fn foo() {
    let f = #[pure]
    |x: i32| x + 1;
    let result = takes_pure_fn(f);
    assert!(result == 2);
    let result = takes_pure_fnmut(f);
    assert!(result == 2);
    let result = takes_pure_fnonce(f);
    assert!(result == 2);
}

#[requires(f.precondition((1i32,)))]
#[ensures(f.postcondition((1i32,), result))]
#[pure]
pub fn takes_pure_fn<F: Fn(i32) -> i32 + FnPure>(f: F) -> i32 {
    f(1)
}

#[requires(f.precondition((1i32,)))]
#[ensures(exists<f2: _> f.postcondition_mut((1i32,), f2, result))]
#[pure]
pub fn takes_pure_fnmut<F: FnMut(i32) -> i32 + FnPure>(mut f: F) -> i32 {
    f(1)
}

#[requires(f.precondition((1i32,)))]
#[ensures(f.postcondition_once((1i32,), result))]
#[pure]
pub fn takes_pure_fnonce<F: FnOnce(i32) -> i32 + FnPure>(f: F) -> i32 {
    f(1)
}
