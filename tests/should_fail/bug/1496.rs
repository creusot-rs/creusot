extern crate creusot_std;

pub fn foo<T>(x: *const T) -> &'static T {
    unsafe { &*x }
}
