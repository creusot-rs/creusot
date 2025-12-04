//! Real numbers
use crate::prelude::*;
#[cfg(creusot)]
use num_rational::BigRational;
use core::{cmp::Ordering, marker::PhantomData};

#[builtin("real.Real.real")]
pub struct Real(PhantomData<*mut ()>);

#[cfg(creusot)]
impl DeepModel for BigRational {
    type DeepModelTy = Real;

    #[logic(opaque)]
    fn deep_model(self) -> Self::DeepModelTy {
        dead
    }
}

impl Real {
    #[logic(opaque)]
    pub fn from_int(_: Int) -> Self {
        dead
    }
}

impl OrdLogic for Real {
    #[logic(open)]
    fn cmp_log(self, o: Self) -> Ordering {
        if self < o {
            Ordering::Less
        } else if self == o {
            Ordering::Equal
        } else {
            Ordering::Greater
        }
    }

    #[logic]
    #[builtin("real.Real.(<=)")]
    fn le_log(self, _: Self) -> bool {
        true
    }

    #[logic]
    #[builtin("real.Real.(<)")]
    fn lt_log(self, _: Self) -> bool {
        true
    }

    #[logic]
    #[builtin("real.Real.(>=)")]
    fn ge_log(self, _: Self) -> bool {
        true
    }

    #[logic]
    #[builtin("real.Real.(>)")]
    fn gt_log(self, _: Self) -> bool {
        true
    }

    crate::logic::ord::ord_laws_impl! {}
}
