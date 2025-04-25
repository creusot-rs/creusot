// NO_REPLAY

extern crate creusot_contracts;
use creusot_contracts::*;

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

pub fn move_mut() {
    #[allow(unused)]
    let mut x = &mut 0u32;

    let mut a = move || {
        #[allow(unused)]
        x = new_ref();
    };
    (a)();
    (a)();
}
