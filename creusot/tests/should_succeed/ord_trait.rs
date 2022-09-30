extern crate creusot_contracts;
use creusot_contracts::*;

#[ensures(result == true)]
pub fn x<T: Ord + DeepModel>(x: &T) -> bool
where
    T::DeepModelTy: OrdLogic,
{
    x <= x
}

#[ensures(result == ((*y).deep_model() <= (*x).deep_model()))]
pub fn gt_or_le<T: Ord + DeepModel>(x: &T, y: &T) -> bool
where
    T::DeepModelTy: OrdLogic,
{
    x >= y
}

#[ensures(result == (@x <= @y))]
pub fn gt_or_le_int(x: usize, y: usize) -> bool {
    x <= y
}
