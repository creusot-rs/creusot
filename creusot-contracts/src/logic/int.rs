use super::model::*;
use crate as creusot_contracts;
use crate::{logic::*, macros::*};

use std::ops::*;

#[cfg_attr(
    feature = "contracts",
    rustc_diagnostic_item = "creusot_int",
    creusot::builtins = "mach.int.Int.int"
)]
pub struct Int(*mut ());

impl Int {
    #[trusted]
    #[logic]
    #[creusot::builtins = "int.Power.power"]
    pub fn pow(self, _: Int) -> Int {
        absurd
    }

    #[trusted]
    #[logic]
    #[creusot::builtins = "int.MinMax.max"]
    pub fn max(self, _: Int) -> Int {
        absurd
    }

    #[trusted]
    #[logic]
    #[creusot::builtins = "int.MinMax.min"]
    pub fn min(self, _: Int) -> Int {
        absurd
    }

    #[trusted]
    #[logic]
    #[creusot::builtins = "int.EuclideanDivision.div"]
    pub fn div_euclid(self, _: Int) -> Int {
        absurd
    }

    #[trusted]
    #[logic]
    #[creusot::builtins = "int.EuclideanDivision.mod"]
    pub fn rem_euclid(self, _: Int) -> Int {
        absurd
    }

    #[logic]
    pub fn abs_diff(self, other: Int) -> Int {
        if self < other {
            other - self
        } else {
            self - other
        }
    }
}

macro_rules! mach_int {
    ($t:ty, $ty_nm:expr) => {
        impl ShallowModel for $t {
            type ShallowModelTy = Int;
            #[logic]
            #[trusted]
            #[creusot::builtins = concat!($ty_nm, ".to_int")]
            fn shallow_model(self) -> Self::ShallowModelTy {
                pearlite! { absurd }
            }
        }

        impl DeepModel for $t {
            type DeepModelTy = Int;
            #[logic]
            fn deep_model(self) -> Self::DeepModelTy {
                pearlite! { @self }
            }
        }
    };
}

mach_int!(u8, "prelude.UInt8");
mach_int!(u16, "prelude.UInt16");
mach_int!(u32, "mach.int.UInt32");
mach_int!(u64, "mach.int.UInt64");
mach_int!(u128, "prelude.UInt128");
mach_int!(usize, "mach.int.UInt64");

mach_int!(i8, "prelude.Int8");
mach_int!(i16, "prelude.Int16");
mach_int!(i32, "mach.int.Int32");
mach_int!(i64, "mach.int.Int64");
mach_int!(i128, "prelude.Int128");
mach_int!(isize, "mach.int.Int64");

#[cfg(feature = "contracts")]
impl Add<Int> for Int {
    type Output = Int;
    #[creusot::no_translate]
    #[creusot::builtins = "add_int"]
    fn add(self, _: Int) -> Self {
        panic!()
    }
}

#[cfg(feature = "contracts")]
impl Sub<Int> for Int {
    type Output = Int;
    #[creusot::no_translate]
    #[creusot::builtins = "sub_int"]
    fn sub(self, _: Int) -> Self {
        panic!()
    }
}

#[cfg(feature = "contracts")]
impl Mul<Int> for Int {
    type Output = Int;
    #[creusot::no_translate]
    #[creusot::builtins = "mul_int"]
    fn mul(self, _: Int) -> Self {
        panic!()
    }
}

#[cfg(feature = "contracts")]
impl Div<Int> for Int {
    type Output = Int;
    #[creusot::no_translate]
    #[creusot::builtins = "div_int"]
    fn div(self, _: Int) -> Self {
        panic!()
    }
}

#[cfg(feature = "contracts")]
impl Rem<Int> for Int {
    type Output = Int;
    #[creusot::no_translate]
    #[creusot::builtins = "rem_int"]
    fn rem(self, _: Int) -> Self {
        panic!()
    }
}

#[cfg(feature = "contracts")]
impl Neg for Int {
    type Output = Int;
    #[creusot::no_translate]
    #[creusot::builtins = "neg_int"]
    fn neg(self) -> Self {
        panic!()
    }
}
