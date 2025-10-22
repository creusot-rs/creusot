// NO_REPLAY

extern crate creusot_contracts;

use creusot_contracts::prelude::*;

pub trait A {
    fn func1(&self, o: &Self) -> bool;
    fn func2(&self, o: &Self) -> bool;
    fn func3(&self, o: &Self) -> bool;
}

#[ensures(result == false)]
pub fn user<T: A>(a: &T, b: &T) -> bool {
    a.func1(b) && b.func2(a) && a.func3(b)
}
