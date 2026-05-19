extern crate creusot_std;
use creusot_std::prelude::*;

#[logic]
#[variant(i)]
pub fn f<T>(i: Int, x: T) {
    f(i, (x, x))
}
