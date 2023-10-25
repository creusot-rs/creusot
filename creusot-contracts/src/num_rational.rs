use std::marker::PhantomData;

use crate::{ghost, open, trusted, DeepModel, ShallowModel, Int, OrdLogic};
use num_rational::{BigRational};
use num::BigInt;
use std::cmp::Ordering;

#[cfg_attr(creusot, creusot::builtins = "prelude.Real.real")]
#[trusted]
pub struct Real(PhantomData<*mut ()>);

#[cfg(creusot)]
impl DeepModel for BigInt {
    type DeepModelTy = Int;

    #[ghost]
    #[open(self)]
    #[trusted]
    fn deep_model(self) -> Self::DeepModelTy {
        absurd
    }
}

#[cfg(creusot)]
impl ShallowModel for BigInt {
    type ShallowModelTy = Int;

    #[ghost]
    #[open]
    fn shallow_model(self) -> Self::ShallowModelTy {
        self.deep_model()
    }
}

#[cfg(creusot)]
impl DeepModel for BigRational {
    type DeepModelTy = Real;

    #[ghost]
    #[open(self)]
    #[trusted]
    fn deep_model(self) -> Self::DeepModelTy {
        absurd
    }
}

impl OrdLogic for Real {
    #[ghost]
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
    #[ghost]
    #[creusot::builtins = "prelude.Real.(<=)"]
    fn le_log(self, _: Self) -> bool {
        true
    }

    #[trusted]
    #[open]
    #[ghost]
    #[creusot::builtins = "prelude.Real.(<)"]
    fn lt_log(self, _: Self) -> bool {
        true
    }

    #[trusted]
    #[open]
    #[ghost]
    #[creusot::builtins = "prelude.Real.(>=)"]
    fn ge_log(self, _: Self) -> bool {
        true
    }

    #[trusted]
    #[open]
    #[ghost]
    #[creusot::builtins = "prelude.Real.(>)"]
    fn gt_log(self, _: Self) -> bool {
        true
    }

    crate::logic::ord::ord_laws_impl! {}
}
