use crate as creusot_contracts;
use crate::*;
use ::std::ops::*;
use num_bigint::BigInt;

impl ShallowModel for num_bigint::BigInt {
    type ShallowModelTy = crate::Int;
    #[logic]
    #[trusted]
    fn shallow_model(self) -> Self::ShallowModelTy {
        pearlite! { absurd }
    }
}

impl DeepModel for num_bigint::BigInt {
    type DeepModelTy = crate::Int;
    #[logic]
    fn deep_model(self) -> Self::DeepModelTy {
        pearlite! { @self }
    }
}

extern_spec! {
    mod num_bigint {
        impl From<i32> for BigInt {
            #[ensures(@result == @i)]
            fn from(i: i32) -> BigInt;
        }

        impl Add<BigInt> for BigInt {
            #[ensures(@result == @self + @rhs)]
            fn add(self, rhs: BigInt) -> BigInt;
        }

        impl Sub<BigInt> for BigInt {
            #[ensures(@result == @self - @rhs)]
            fn sub(self, rhs: BigInt) -> BigInt;
        }

        impl Mul<BigInt> for BigInt {
            #[ensures(@result == @self * @rhs)]
            fn mul(self, rhs: BigInt) -> BigInt;
        }

        impl Div<BigInt> for BigInt {
            #[requires(@rhs != 0)]
            #[ensures(@result == @self / @rhs)]
            fn div(self, rhs: BigInt) -> BigInt;
        }
    }
}
