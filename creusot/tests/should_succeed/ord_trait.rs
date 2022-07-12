extern crate creusot_contracts;
use creusot_contracts::{std::cmp::Ord, *};

#[ensures(result == true)]
pub fn x<T: Ord>(x: &T) -> bool {
    x.le(x)
}

#[ensures(result == (*y <= *x))]
pub fn gt_or_le<T: Ord>(x: &T, y: &T) -> bool {
    x.ge(y)
}

#[ensures(result == (@x <= @y))]
pub fn gt_or_le_int(x: usize, y: usize) -> bool {
    x <= y
}
