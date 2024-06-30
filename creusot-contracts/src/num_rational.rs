use std::marker::PhantomData;

use crate::{logic, open, pearlite, trusted, EqModel, Int, OrdLogic};
use num_rational::BigRational;
use std::cmp::Ordering;

#[cfg_attr(creusot, creusot::builtins = "prelude.Real.real")]
#[trusted]
pub struct Real(PhantomData<*mut ()>);

#[cfg(creusot)]
impl EqModel for BigRational {
    type EqModelTy = Real;

    #[logic]
    #[open(self)]
    #[trusted]
    fn eq_model(self) -> Self::EqModelTy {
        absurd
    }
}

impl Real {
    #[logic]
    #[trusted]
    #[open(self)]
    pub fn from_int(_: Int) -> Self {
        pearlite! { absurd }
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
    #[creusot::builtins = "prelude.Real.(<=)"]
    fn le_log(self, _: Self) -> bool {
        true
    }

    #[trusted]
    #[open]
    #[logic]
    #[creusot::builtins = "prelude.Real.(<)"]
    fn lt_log(self, _: Self) -> bool {
        true
    }

    #[trusted]
    #[open]
    #[logic]
    #[creusot::builtins = "prelude.Real.(>=)"]
    fn ge_log(self, _: Self) -> bool {
        true
    }

    #[trusted]
    #[open]
    #[logic]
    #[creusot::builtins = "prelude.Real.(>)"]
    fn gt_log(self, _: Self) -> bool {
        true
    }

    crate::logic::ord::ord_laws_impl! {}
}
