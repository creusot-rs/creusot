extern crate creusot_std;
use creusot_std::prelude::*;

#[requires(|mode| f.precondition(mode, (1i32,)))]
#[ensures(|result, mode| f.postcondition(mode, (1i32,), result))]
fn call_with_one<F: Fn(i32) -> i32>(mut f: F) -> i32 {
    f(1)
}

#[requires(|mode| (*f).precondition(mode, (1i32,)))]
#[ensures(|result, mode| (*f).postcondition_mut(mode, (1i32,), ^f, result))]
fn call_with_one_mut<F: FnMut(i32) -> i32>(f: &mut F) -> i32 {
    f(1)
}

#[requires(|mode| f.precondition(mode, (1i32,)))]
#[ensures(|result, mode| f.postcondition_once(mode, (1i32,), result))]
fn call_with_one_once<F: FnOnce(i32) -> i32>(mut f: F) -> i32 {
    f(1)
}

pub fn closure_fn() {
    let mut f = |x: i32| x + 1;

    assert!(call_with_one(f) == 2);
    assert!(call_with_one_mut(&mut f) == 2);
    assert!(call_with_one_once(f) == 2);
}

pub fn closure_fn_mut() {
    let mut y = 0;
    let mut f = |x: i32| {
        y += x;
        y
    };

    assert!(call_with_one_mut(&mut f) == 1);
    assert!(call_with_one_once(f) == 2);
    assert!(y == 2);
}

pub fn closure_fn_once() {
    let y = Box::new(2);
    let mut z = 0;
    let f = move |x: i32| {
        let move_y = y;
        z += *move_y + x;
        z
    };

    assert!(call_with_one_once(f) == 3);
    assert!(z == 0);
}
