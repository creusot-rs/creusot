extern crate creusot_std;

use creusot_std::prelude::*;

pub trait T where
    Self: Ord + DeepModel + Sized,
    <Self as DeepModel>::DeepModelTy: OrdLogic,
{
    #[logic]
    fn greater_or_eq_logic(x: &Self, y: &Self) -> bool {
        (*x).deep_model() >= (*y).deep_model()
    }

    #[logic_alias(Self::greater_or_eq_logic)]
    fn greater_or_eq(x: &Self, y: &Self) -> bool;
}

impl T for i64 {
    #[logic_alias(Self::greater_or_eq_logic)]
    fn greater_or_eq(lhs: &i64, rhs: &i64) -> bool {
        lhs.ge(rhs)
    }
}

impl T for i32 {
    #[logic_alias(Self::greater_or_eq_logic)]
    fn greater_or_eq(lhs: &i32, rhs: &i32) -> bool {
        lhs.ge(rhs)
    }
}

#[ensures(result == !i64::greater_or_eq(lhs, rhs))]
pub fn less_than_i64(lhs: &i64, rhs: &i64) -> bool {
    lhs < rhs
}

#[ensures(result == !i32::greater_or_eq(lhs, rhs))]
pub fn less_than_i32(lhs: &i32, rhs: &i32) -> bool {
    lhs < rhs
}
