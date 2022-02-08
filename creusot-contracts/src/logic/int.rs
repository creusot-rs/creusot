use super::model::*;
use crate::logic::*;

use creusot_contracts_proc::*;

use std::ops::*;

#[rustc_diagnostic_item = "creusot_int"]
pub struct Int(*mut ());

impl WellFounded for Int {}

impl Int {
    #[trusted]
    #[logic]
    #[creusot::builtins = "int.Power.power"]
    pub fn pow(self, _: Int) -> Int {
        std::process::abort()
    }
}

impl From<u32> for Int {
    #[logic]
    #[trusted]
    #[rustc_diagnostic_item = "u32_to_int"]
    #[creusot::builtins = "mach.int.UInt32.to_int"]
    fn from(_: u32) -> Self {
        std::process::abort()
    }
}
impl Model for u32 {
    type ModelTy = Int;
    #[logic]
    #[rustc_diagnostic_item = "u32_model"]
    #[creusot::builtins = "mach.int.UInt32.to_int"]
    fn model(self) -> Self::ModelTy {
        Int::from(self)
    }
}

impl From<i32> for Int {
    #[logic]
    #[trusted]
    #[rustc_diagnostic_item = "i32_to_int"]
    #[creusot::builtins = "mach.int.Int32.to_int"]
    fn from(_: i32) -> Self {
        std::process::abort()
    }
}
impl Model for i32 {
    type ModelTy = Int;
    #[logic]
    #[rustc_diagnostic_item = "i32_model"]
    #[creusot::builtins = "mach.int.Int32.to_int"]
    fn model(self) -> Self::ModelTy {
        Int::from(self)
    }
}

impl From<usize> for Int {
    #[logic]
    #[trusted]
    #[rustc_diagnostic_item = "usize_to_int"]
    #[creusot::builtins = "mach.int.UInt64.to_int"]
    fn from(_: usize) -> Self {
        std::process::abort()
    }
}
impl Model for usize {
    type ModelTy = Int;
    #[logic]
    #[rustc_diagnostic_item = "usize_model"]
    #[creusot::builtins = "mach.int.UInt64.to_int"]
    fn model(self) -> Self::ModelTy {
        Int::from(self)
    }
}

impl From<isize> for Int {
    #[logic]
    #[trusted]
    #[rustc_diagnostic_item = "isize_to_int"]
    fn from(_: isize) -> Self {
        std::process::abort()
    }
}
impl Model for isize {
    type ModelTy = Int;
    #[logic]
    #[rustc_diagnostic_item = "isize_model"]
    #[creusot::builtins = "mach.int.Int64.to_int"]
    fn model(self) -> Self::ModelTy {
        Int::from(self)
    }
}

impl Add<Int> for Int {
    type Output = Int;
    #[creusot::no_translate]
    #[rustc_diagnostic_item = "add_int"]
    fn add(self, _: Int) -> Self {
        panic!()
    }
}

impl Sub<Int> for Int {
    type Output = Int;
    #[creusot::no_translate]
    #[rustc_diagnostic_item = "sub_int"]
    fn sub(self, _: Int) -> Self {
        panic!()
    }
}

impl Mul<Int> for Int {
    type Output = Int;
    #[creusot::no_translate]
    #[rustc_diagnostic_item = "mul_int"]
    fn mul(self, _: Int) -> Self {
        panic!()
    }
}

impl Div<Int> for Int {
    type Output = Int;
    #[creusot::no_translate]
    #[rustc_diagnostic_item = "div_int"]
    fn div(self, _: Int) -> Self {
        panic!()
    }
}

impl Rem<Int> for Int {
    type Output = Int;
    #[creusot::no_translate]
    #[rustc_diagnostic_item = "rem_int"]
    fn rem(self, _: Int) -> Self {
        panic!()
    }
}

impl Neg for Int {
    type Output = Int;
    #[creusot::no_translate]
    #[rustc_diagnostic_item = "neg_int"]
    fn neg(self) -> Self {
        panic!()
    }
}
