extern crate creusot_std;

use creusot_std::prelude::*;

pub trait A {
    #[ensures(result == true)]
    fn is_true(&self) -> bool;
}

#[ensures(result == true)]
pub fn omg<T: A>(a: T) -> bool {
    a.is_true()
}
