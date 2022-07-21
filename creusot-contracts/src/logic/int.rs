use super::model::*;
use crate as creusot_contracts;
use crate::logic::*;
use creusot_contracts_proc::*;

use std::ops::*;

#[rustc_diagnostic_item = "creusot_int"]
#[derive(std::clone::Clone, Copy)]
pub struct Int(*mut ());

impl WellFounded for Int {}

impl Int {
    #[trusted]
    #[logic]
    #[creusot::builtins = "int.Power.power"]
    pub fn pow(self, _: Int) -> Int {
        absurd
    }
}

macro_rules! mach_int {
    ($t:ty, $ty_nm:expr) => {
        impl Model for $t {
            type ModelTy = Int;
            #[logic]
            #[creusot::builtins = concat!($ty_nm, ".to_int")]
            fn model(self) -> Self::ModelTy {
                Int::from(self)
            }
        }

        impl From<$t> for Int {
            #[logic]
            #[trusted]
            #[creusot::builtins = concat!($ty_nm, ".to_int")]
            fn from(_: $t) -> Self {
                absurd
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

impl Add<Int> for Int {
    type Output = Int;
    #[creusot::no_translate]
    #[creusot::builtins = "add_int"]
    fn add(self, _: Int) -> Self {
        panic!()
    }
}

impl Sub<Int> for Int {
    type Output = Int;
    #[creusot::no_translate]
    #[creusot::builtins = "sub_int"]
    fn sub(self, _: Int) -> Self {
        panic!()
    }
}

impl Mul<Int> for Int {
    type Output = Int;
    #[creusot::no_translate]
    #[creusot::builtins = "mul_int"]
    fn mul(self, _: Int) -> Self {
        panic!()
    }
}

impl Div<Int> for Int {
    type Output = Int;
    #[creusot::no_translate]
    #[creusot::builtins = "div_int"]
    fn div(self, _: Int) -> Self {
        panic!()
    }
}

impl Rem<Int> for Int {
    type Output = Int;
    #[creusot::no_translate]
    #[creusot::builtins = "rem_int"]
    fn rem(self, _: Int) -> Self {
        panic!()
    }
}

impl Neg for Int {
    type Output = Int;
    #[creusot::no_translate]
    #[creusot::builtins = "neg_int"]
    fn neg(self) -> Self {
        panic!()
    }
}
