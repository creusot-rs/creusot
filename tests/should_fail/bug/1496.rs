extern crate creusot_contracts;

pub fn foo<T>(x: *const T) -> &'static T {
    unsafe { &*x }
}
