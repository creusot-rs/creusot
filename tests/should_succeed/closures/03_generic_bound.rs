// NO_REPLAY

extern crate creusot_std;

fn closure_param<F: Fn(u32)>(f: F) {
    (f)(0)
}

pub fn caller() {
    closure_param(|_x: u32| ())
}
