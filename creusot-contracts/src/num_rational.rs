//! Real numbers
use crate::*;
use ::num_rational::BigRational;
use ::std::{cmp::Ordering, marker::PhantomData};

#[cfg_attr(creusot, creusot::builtins = "real.Real.real")]
#[trusted]
pub struct Real(PhantomData<*mut ()>);

#[cfg(creusot)]
impl DeepModel for BigRational {
    type DeepModelTy = Real;

    #[logic]
    #[trusted]
    fn deep_model(self) -> Self::DeepModelTy {
        dead
    }
}

impl Real {
    #[logic]
    #[trusted]
    pub fn from_int(_: Int) -> Self {
        dead
    }
}

impl OrdLogic for Real {
    #[logic]
    #[open]
    fn cmp_log(self, o: Self) -> Ordering {
        if self < o {
            Ordering::Less
        } else if self == o {
            Ordering::Equal
        } else {
            Ordering::Greater
        }
    }

    #[trusted]
    #[open]
    #[logic]
    #[creusot::builtins = "real.Real.(<=)"]
    fn le_log(self, _: Self) -> bool {
        true
    }

    #[trusted]
    #[open]
    #[logic]
    #[creusot::builtins = "real.Real.(<)"]
    fn lt_log(self, _: Self) -> bool {
        true
    }

    #[trusted]
    #[open]
    #[logic]
    #[creusot::builtins = "real.Real.(>=)"]
    fn ge_log(self, _: Self) -> bool {
        true
    }

    #[trusted]
    #[open]
    #[logic]
    #[creusot::builtins = "real.Real.(>)"]
    fn gt_log(self, _: Self) -> bool {
        true
    }

    crate::logic::ord::ord_laws_impl! {}
}
