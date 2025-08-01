extern crate creusot_contracts;
use creusot_contracts::*;

pub fn foo() {
    let f = #[pure]
    |x: i32| x + 1;
    let result = takes_ghost_fn(f);
    assert!(result == 2);
    let result = takes_ghost_fnmut(f);
    assert!(result == 2);
    let result = takes_ghost_fnonce(f);
    assert!(result == 2);
}

#[requires(f.precondition((1i32,)))]
#[ensures(f.postcondition((1i32,), result))]
#[pure]
pub fn takes_ghost_fn<F: Fn(i32) -> i32 + FnGhost>(f: F) -> i32 {
    f(1)
}

#[requires(f.precondition((1i32,)))]
#[ensures(exists<f2> f.postcondition_mut((1i32,), f2, result))]
#[pure]
pub fn takes_ghost_fnmut<F: FnMut(i32) -> i32 + FnGhost>(mut f: F) -> i32 {
    f(1)
}

#[requires(f.precondition((1i32,)))]
#[ensures(f.postcondition_once((1i32,), result))]
#[pure]
pub fn takes_ghost_fnonce<F: FnOnce(i32) -> i32 + FnGhost>(f: F) -> i32 {
    f(1)
}
