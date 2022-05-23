use super::model::*;
use crate as creusot_contracts;
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
        absurd
    }
}

impl From<u8> for Int {
    #[logic]
    #[trusted]
    #[creusot::builtins = "prelude.UInt8.to_int"]
    fn from(_: u8) -> Self {
        absurd
    }
}
impl Model for u8 {
    type ModelTy = Int;
    #[logic]
    #[creusot::builtins = "prelude.UInt8.to_int"]
    fn model(self) -> Self::ModelTy {
        Int::from(self)
    }
}

impl From<u32> for Int {
    #[logic]
    #[trusted]
    #[creusot::builtins = "mach.int.UInt32.to_int"]
    fn from(_: u32) -> Self {
        absurd
    }
}
impl Model for u32 {
    type ModelTy = Int;
    #[logic]
    #[creusot::builtins = "mach.int.UInt32.to_int"]
    fn model(self) -> Self::ModelTy {
        Int::from(self)
    }
}

impl From<u64> for Int {
    #[logic]
    #[trusted]
    #[creusot::builtins = "mach.int.UInt64.to_int"]
    fn from(_: u64) -> Self {
        absurd
    }
}
impl Model for u64 {
    type ModelTy = Int;
    #[logic]
    #[creusot::builtins = "mach.int.UInt64.to_int"]
    fn model(self) -> Self::ModelTy {
        Int::from(self)
    }
}

impl From<i64> for Int {
    #[logic]
    #[trusted]
    #[creusot::builtins = "mach.int.Int64.to_int"]
    fn from(_: i64) -> Self {
        absurd
    }
}
impl Model for i64 {
    type ModelTy = Int;
    #[logic]
    #[creusot::builtins = "mach.int.Int64.to_int"]
    fn model(self) -> Self::ModelTy {
        Int::from(self)
    }
}

impl From<i32> for Int {
    #[logic]
    #[trusted]
    #[creusot::builtins = "mach.int.Int32.to_int"]
    fn from(_: i32) -> Self {
        absurd
    }
}
impl Model for i32 {
    type ModelTy = Int;
    #[logic]
    #[creusot::builtins = "mach.int.Int32.to_int"]
    fn model(self) -> Self::ModelTy {
        Int::from(self)
    }
}

impl From<usize> for Int {
    #[logic]
    #[trusted]
    #[creusot::builtins = "mach.int.UInt64.to_int"]
    fn from(_: usize) -> Self {
        absurd
    }
}
impl Model for usize {
    type ModelTy = Int;
    #[logic]
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
        absurd
    }
}
impl Model for isize {
    type ModelTy = Int;
    #[logic]
    #[creusot::builtins = "mach.int.Int64.to_int"]
    fn model(self) -> Self::ModelTy {
        Int::from(self)
    }
}

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
