//! Real numbers
use crate::{
    invariant::{InhabitedInvariant, Subset},
    logic::ops::{AddLogic, DivLogic, MulLogic, NegLogic, SubLogic},
    prelude::*,
};
#[cfg(all(creusot, feature = "std"))]
use num_rational::BigRational;

#[builtin("real.Real.real")]
pub struct Real;

#[cfg(all(creusot, feature = "std"))]
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

impl PartialOrdLogic for Real {
    #[logic]
    #[builtin("real.Real.(<)")]
    fn lt_log(self, _: Self) -> bool {
        dead
    }

    #[logic]
    #[builtin("real.Real.(<=)")]
    fn le_log(self, _: Self) -> bool {
        dead
    }

    #[logic]
    #[ensures(!(self < self))]
    fn irreflexive(self) {}

    #[logic]
    #[requires(x < y)]
    #[requires(y < z)]
    #[ensures(x < z)]
    fn transitive(x: Self, y: Self, z: Self) {}

    #[logic]
    #[ensures((self <= other) == (self < other || self == other))]
    fn le_lt_log(self, other: Self) {}
}

impl OrdLogic for Real {
    #[logic]
    #[ensures(self < other || self == other || other < self)]
    fn lt_log_total(self, other: Self) {}
}

impl AddLogic for Real {
    type Output = Self;
    #[logic]
    #[builtin("real.Real.(+)")]
    #[allow(unused_variables)]
    fn add_logic(self, other: Self) -> Self {
        dead
    }
}

impl SubLogic for Real {
    type Output = Self;
    #[logic]
    #[builtin("real.Real.(-)")]
    #[allow(unused_variables)]
    fn sub_logic(self, other: Self) -> Self {
        dead
    }
}

impl MulLogic for Real {
    type Output = Self;
    #[logic]
    #[builtin("real.Real.(*)")]
    #[allow(unused_variables)]
    fn mul_logic(self, other: Self) -> Self {
        dead
    }
}

impl DivLogic for Real {
    type Output = Self;
    #[logic]
    #[builtin("real.Real.(/)")]
    #[allow(unused_variables)]
    fn div_logic(self, other: Self) -> Self {
        dead
    }
}

impl NegLogic for Real {
    type Output = Self;
    #[logic]
    #[builtin("real.Real.(-_)")]
    fn neg_logic(self) -> Self {
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
    #[ensures(#[trigger(self == other)] result == (self == other))]
    pub fn ext_eq(self, other: Self) -> bool {
        let _ = Subset::<PositiveRealInner>::inner_inj;
        self.to_real() == other.to_real()
    }

    #[logic(open, inline)]
    pub fn from_int(i: Int) -> Self {
        Self::new(Real::from_int(i))
    }
}

impl PartialOrdLogic for PositiveReal {
    #[logic(open)]
    fn le_log(self, o: Self) -> bool {
        self.to_real() <= o.to_real()
    }

    #[logic(open)]
    fn lt_log(self, o: Self) -> bool {
        self.to_real() < o.to_real()
    }

    #[logic]
    #[ensures(!(self < self))]
    fn irreflexive(self) {}

    #[logic]
    #[requires(x < y)]
    #[requires(y < z)]
    #[ensures(x < z)]
    fn transitive(x: Self, y: Self, z: Self) {}

    #[logic(law)]
    #[ensures((self <= other) == (self < other || self == other))]
    fn le_lt_log(self, other: Self) {
        let _ = PositiveReal::ext_eq;
    }
}

impl OrdLogic for PositiveReal {
    #[logic(law)]
    #[ensures(self < other || self == other || other < self)]
    fn lt_log_total(self, other: Self) {
        let _ = PositiveReal::ext_eq;
    }
}

impl AddLogic for PositiveReal {
    type Output = Self;
    #[logic]
    #[ensures(result.to_real() == self.to_real() + other.to_real())]
    fn add_logic(self, other: Self) -> Self {
        Self::new(self.to_real() + other.to_real())
    }
}

impl MulLogic for PositiveReal {
    type Output = Self;
    #[logic]
    #[ensures(result.to_real() == self.to_real() * other.to_real())]
    fn mul_logic(self, other: Self) -> Self {
        Self::new(self.to_real() * other.to_real())
    }
}

impl DivLogic for PositiveReal {
    type Output = Self;
    #[logic]
    #[ensures(result.to_real() == self.to_real() / other.to_real())]
    fn div_logic(self, other: Self) -> Self {
        Self::new(self.to_real() / other.to_real())
    }
}
