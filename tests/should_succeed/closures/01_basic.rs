// NO_REPLAY

extern crate creusot_std;
use creusot_std::prelude::*;

pub fn uses_closure() {
    let y = true;
    let _x = (|| y)();
}

pub fn multi_arg() {
    let x = |a, b| a + b;
    let _a = (x)(0, 3);
}

// Sadly, the unnesting predicate is weakened when we capture things by *value*
// even if we treat it like a reference capture.
pub fn move_closure() {
    let a = &mut 0i32;

    let mut x = move || {
        *a += 1;
    };

    (x)();
    (x)();
}

#[trusted]
pub fn new_ref<'a, T>() -> &'a mut T {
    panic!()
}

#[allow(unused)]
pub fn move_mut() {
    let mut x = &mut 0u32;

    let mut a = move || {
        x = new_ref();
    };
    (a)();
    (a)();
}
