//! Real numbers
use crate::{
    invariant::{InhabitedInvariant, Subset},
    logic::ops::{AddLogic, DivLogic, MulLogic, NegLogic, SubLogic},
    prelude::*,
};
use core::cmp::Ordering;
#[cfg(creusot)]
use num_rational::BigRational;

#[builtin("real.Real.real")]
pub struct Real;

#[cfg(creusot)]
impl DeepModel for BigRational {
    type DeepModelTy = Real;

    #[logic(opaque)]
    fn deep_model(self) -> Self::DeepModelTy {
        dead
    }
}

impl Real {
    #[logic]
    #[builtin("real.FromInt.from_int")]
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

impl AddLogic for Real {
    type Output = Self;
    #[logic]
    #[builtin("real.Real.(+)")]
    #[allow(unused_variables)]
    fn add(self, other: Self) -> Self {
        dead
    }
}

impl SubLogic for Real {
    type Output = Self;
    #[logic]
    #[builtin("real.Real.(-)")]
    #[allow(unused_variables)]
    fn sub(self, other: Self) -> Self {
        dead
    }
}

impl MulLogic for Real {
    type Output = Self;
    #[logic]
    #[builtin("real.Real.(*)")]
    #[allow(unused_variables)]
    fn mul(self, other: Self) -> Self {
        dead
    }
}

impl DivLogic for Real {
    type Output = Self;
    #[logic]
    #[builtin("real.Real.(/)")]
    #[allow(unused_variables)]
    fn div(self, other: Self) -> Self {
        dead
    }
}

impl NegLogic for Real {
    type Output = Self;
    #[logic]
    #[builtin("real.Real.(-_)")]
    fn neg(self) -> Self {
        dead
    }
}

struct PositiveRealInner(Real);

impl Invariant for PositiveRealInner {
    #[logic]
    fn invariant(self) -> bool {
        self.0 > Real::from_int(0)
    }
}

impl InhabitedInvariant for PositiveRealInner {
    #[logic]
    #[ensures(result.invariant())]
    fn inhabits() -> Self {
        Self(Real::from_int(1))
    }
}

/// Natural numbers, i.e., integers that are greater or equal to 0.
pub struct PositiveReal(Subset<PositiveRealInner>);

impl PositiveReal {
    #[logic]
    #[ensures(result > Real::from_int(0))]
    pub fn to_real(self) -> Real {
        pearlite! { self.0.inner().0 }
    }

    #[logic]
    #[requires(n > Real::from_int(0))]
    #[ensures(result.to_real() == n)]
    pub fn new(n: Real) -> PositiveReal {
        PositiveReal(Subset::new_logic(PositiveRealInner(n)))
    }

    #[logic(open)]
    #[ensures(result == (self == other))]
    pub fn ext_eq(self, other: Self) -> bool {
        let _ = Subset::<PositiveRealInner>::inner_inj;
        self.to_real() == other.to_real()
    }

    #[logic(open, inline)]
    pub fn from_int(i: Int) -> Self {
        Self::new(Real::from_int(i))
    }
}

impl OrdLogic for PositiveReal {
    #[logic(open)]
    fn cmp_log(self, o: Self) -> Ordering {
        self.to_real().cmp_log(o.to_real())
    }

    #[logic(open)]
    fn le_log(self, o: Self) -> bool {
        self.to_real().le_log(o.to_real())
    }

    #[logic(open)]
    fn lt_log(self, o: Self) -> bool {
        self.to_real().lt_log(o.to_real())
    }

    #[logic(open)]
    fn ge_log(self, o: Self) -> bool {
        self.to_real().ge_log(o.to_real())
    }

    #[logic(open)]
    fn gt_log(self, o: Self) -> bool {
        self.to_real().gt_log(o.to_real())
    }

    crate::logic::ord::ord_laws_impl! { let _ = PositiveReal::ext_eq; }
}

impl AddLogic for PositiveReal {
    type Output = Self;
    #[logic]
    #[ensures(result.to_real() == self.to_real() + other.to_real())]
    fn add(self, other: Self) -> Self {
        Self::new(self.to_real() + other.to_real())
    }
}

impl MulLogic for PositiveReal {
    type Output = Self;
    #[logic]
    #[ensures(result.to_real() == self.to_real() * other.to_real())]
    fn mul(self, other: Self) -> Self {
        Self::new(self.to_real() * other.to_real())
    }
}

impl DivLogic for PositiveReal {
    type Output = Self;
    #[logic]
    #[ensures(result.to_real() == self.to_real() / other.to_real())]
    fn div(self, other: Self) -> Self {
        Self::new(self.to_real() / other.to_real())
    }
}
