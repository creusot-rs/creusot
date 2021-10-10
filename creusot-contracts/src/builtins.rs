use crate as creusot_contracts;
use creusot_contracts_proc::*;

pub trait Model {
    type ModelTy;
    #[logic_rust]
    fn model(self) -> Self::ModelTy;
}

impl<T: Model> Model for &T {
    type ModelTy = T::ModelTy;
    #[logic_rust]
    fn model(self) -> Self::ModelTy {
        (*self).model()
    }
}

impl<T: Model> Model for &mut T {
    type ModelTy = T::ModelTy;
    #[logic_rust]
    fn model(self) -> Self::ModelTy {
        (*self).model()
    }
}

#[rustc_diagnostic_item = "creusot_int"]
pub struct Int;

impl PartialEq for Int {
    #[creusot::spec::no_translate]
    #[rustc_diagnostic_item = "eq_int"]
    fn eq(&self, _: &Int) -> bool {
        panic!()
    }

    #[creusot::spec::no_translate]
    #[rustc_diagnostic_item = "ne_int"]
    fn ne(&self, _: &Int) -> bool {
        panic!()
    }
}

impl PartialOrd for Int {
    #[creusot::spec::no_translate]
    #[rustc_diagnostic_item = "le_int"]
    fn le(&self, _: &Int) -> bool {
        panic!()
    }

    #[creusot::spec::no_translate]
    #[rustc_diagnostic_item = "ge_int"]
    fn ge(&self, _: &Int) -> bool {
        panic!()
    }

    #[creusot::spec::no_translate]
    #[rustc_diagnostic_item = "lt_int"]
    fn lt(&self, _: &Int) -> bool {
        panic!()
    }

    #[creusot::spec::no_translate]
    #[rustc_diagnostic_item = "gt_int"]
    fn gt(&self, _: &Int) -> bool {
        panic!()
    }

    #[creusot::spec::no_translate]
    fn partial_cmp(&self, _: &Self) -> Option<std::cmp::Ordering> {
        panic!()
    }
}

impl From<i32> for Int {
    #[creusot::spec::no_translate]
    #[rustc_diagnostic_item = "i32_to_int"]
    fn from(_: i32) -> Self {
        panic!()
    }
}
impl Model for i32 {
    type ModelTy = Int;
    #[logic_rust]
    fn model(self) -> Self::ModelTy {
        Int::from(self)
    }
}

impl From<u32> for Int {
    #[creusot::spec::no_translate]
    #[rustc_diagnostic_item = "u32_to_int"]
    fn from(_: u32) -> Self {
        panic!()
    }
}
impl Model for u32 {
    type ModelTy = Int;
    #[logic_rust]
    fn model(self) -> Self::ModelTy {
        Int::from(self)
    }
}

impl From<usize> for Int {
    #[creusot::spec::no_translate]
    #[rustc_diagnostic_item = "usize_to_int"]
    fn from(_: usize) -> Self {
        panic!()
    }
}
impl Model for usize {
    type ModelTy = Int;
    #[logic_rust]
    fn model(self) -> Self::ModelTy {
        Int::from(self)
    }
}

impl From<isize> for Int {
    #[creusot::spec::no_translate]
    #[rustc_diagnostic_item = "isize_to_int"]
    fn from(_: isize) -> Self {
        panic!()
    }
}
impl Model for isize {
    type ModelTy = Int;
    #[logic_rust]
    fn model(self) -> Self::ModelTy {
        Int::from(self)
    }
}

use std::ops::*;

impl Add<Int> for Int {
    type Output = Int;
    #[creusot::spec::no_translate]
    #[rustc_diagnostic_item = "add_int"]
    fn add(self, _: Int) -> Self {
        panic!()
    }
}

impl Sub<Int> for Int {
    type Output = Int;
    #[creusot::spec::no_translate]
    #[rustc_diagnostic_item = "sub_int"]
    fn sub(self, _: Int) -> Self {
        panic!()
    }
}

impl Mul<Int> for Int {
    type Output = Int;
    #[creusot::spec::no_translate]
    #[rustc_diagnostic_item = "mul_int"]
    fn mul(self, _: Int) -> Self {
        panic!()
    }
}

impl Div<Int> for Int {
    type Output = Int;
    #[creusot::spec::no_translate]
    #[rustc_diagnostic_item = "div_int"]
    fn div(self, _: Int) -> Self {
        panic!()
    }
}

impl Rem<Int> for Int {
    type Output = Int;
    #[creusot::spec::no_translate]
    #[rustc_diagnostic_item = "rem_int"]
    fn rem(self, _: Int) -> Self {
        panic!()
    }
}

impl Neg for Int {
    type Output = Int;
    #[creusot::spec::no_translate]
    #[rustc_diagnostic_item = "neg_int"]
    fn neg(self) -> Self {
        panic!()
    }
}

#[rustc_diagnostic_item = "creusot_resolve"]
pub unsafe trait Resolve {
    #[predicate_rust]
    #[rustc_diagnostic_item = "creusot_resolve_method"]
    fn resolve(self) -> bool;
}

unsafe impl<T1: Resolve, T2: Resolve> Resolve for (T1, T2) {
    #[predicate_rust]
    fn resolve(self) -> bool {
        Resolve::resolve(self.0) && Resolve::resolve(self.1)
    }
}

unsafe impl<T> Resolve for &mut T {
    predicate! {
        fn resolve(self) -> bool {
            ^self === *self
        }
    }
}
