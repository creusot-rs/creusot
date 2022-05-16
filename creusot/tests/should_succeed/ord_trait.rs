extern crate creusot_contracts;
use creusot_contracts::std::*;
use creusot_contracts::*;

#[ensures(result == true)]
fn x<T: Ord>(x: &T) -> bool {
    x.le(x)
}

#[ensures(result == (*y <= *x))]
fn gt_or_le<T: Ord>(x: &T, y: &T) -> bool {
    x.ge(y)
}

#[ensures(result == (@x <= @y))]
fn gt_or_le_int(x: usize, y: usize) -> bool {
    x <= y
}
