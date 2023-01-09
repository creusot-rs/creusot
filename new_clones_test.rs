extern crate creusot_contracts;
use creusot_contracts::*;

pub fn move_closure() {
    let a = &mut 0i32;

    let mut x = move || {
        *a += 1;
    };

    (x)();
    (x)();
}
