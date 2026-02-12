use creusot_std::prelude::*;

#[ensures(true)]
pub fn foo<T>(x: &T) -> *const T {
    x
}
