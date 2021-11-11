#![feature(unsized_fn_params)]
extern crate creusot_contracts;
use creusot_contracts::std::*;
use creusot_contracts::*;

#[ensures(result === true)]
fn x<T: Ord>(x: &T) -> bool {
    proof_assert! { {OrdLogic::refl(*x); true} };
    x.le(x)
}

#[ensures(result === *y <= *x)]
fn gt_or_le<T: Ord>(x: &T, y: &T) -> bool {
    proof_assert! { {OrdLogic::antisym1(*x, *y); true} };
    proof_assert! { {OrdLogic::antisym2(*x, *y); true} };
    proof_assert! { {EqLogic::symmetry(*x, *x); true} };
    x.ge(y)
}

#[ensures(result === @x <= @y)]
fn gt_or_le_int(x: usize, y: usize) -> bool {
    x <= y
}
