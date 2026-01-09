extern crate creusot_std;
#[allow(unused)]
use creusot_std::prelude::*;

#[allow(unused_assignments)]
pub fn maybe_uninit<T: Default>(b: bool, y: T) -> T {
    let mut x: T;
    if b {
        x = T::default();
    }
    // do not resolve x here as it is maybe uninit
    x = y;
    x
}

pub fn init_join(b: bool, mut x: i32) {
    let y: &mut i32;
    let z: &mut i32;

    if b {
        z = &mut x;
        y = &mut *z;
        // resolve z here
    } else {
        y = &mut x;
    }

    *y = 5;
    assert!(x == 5);
}
