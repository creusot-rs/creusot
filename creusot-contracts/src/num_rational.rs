use std::marker::PhantomData;

use crate::{ghost, logic, open, trusted, DeepModel, OrdLogic};
use num_rational::BigRational;
use std::cmp::Ordering;

#[cfg_attr(creusot, creusot::builtins = "prelude.Real.real")]
#[trusted]
pub struct Real(PhantomData<*mut ()>);

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

    #[ghost]
    #[open(self)]
    fn cmp_le_log(_: Self, _: Self) {
        ()
    }

    #[ghost]
    #[open(self)]
    fn cmp_lt_log(_: Self, _: Self) {
        ()
    }

    #[ghost]
    #[open(self)]
    fn cmp_ge_log(_: Self, _: Self) {
        ()
    }

    #[ghost]
    #[open(self)]
    fn cmp_gt_log(_: Self, _: Self) {
        ()
    }

    #[ghost]
    #[open(self)]
    fn refl(_: Self) {
        ()
    }

    #[ghost]
    #[open(self)]
    fn trans(_: Self, _: Self, _: Self, _: Ordering) {
        ()
    }

    #[ghost]
    #[open(self)]
    fn antisym1(_: Self, _: Self) {
        ()
    }

    #[ghost]
    #[open(self)]
    fn antisym2(_: Self, _: Self) {
        ()
    }

    #[ghost]
    #[open(self)]
    fn eq_cmp(_: Self, _: Self) {
        ()
    }
}
