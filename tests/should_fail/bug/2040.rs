extern crate creusot_std;
use creusot_std::prelude::*;

pub fn f<T: Eq>(x: T) -> bool {
    x == x
}
