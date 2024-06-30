extern crate creusot_contracts;
use creusot_contracts::{logic::OrdLogic, *};

#[ensures(result == true)]
pub fn x<T: Ord + EqModel>(x: &T) -> bool
where
    T::EqModelTy: OrdLogic,
{
    x <= x
}

#[ensures(result == ((*y).eq_model() <= (*x).eq_model()))]
pub fn gt_or_le<T: Ord + EqModel>(x: &T, y: &T) -> bool
where
    T::EqModelTy: OrdLogic,
{
    x >= y
}

#[ensures(result == (x@ <= y@))]
pub fn gt_or_le_int(x: usize, y: usize) -> bool {
    x <= y
}
