use crate::{
    std::ops::{Add, Div, Mul, Neg, Rem, Sub},
    *,
};

#[cfg_attr(creusot, rustc_diagnostic_item = "creusot_int", creusot::builtins = "prelude.Int.int")]
#[allow(dead_code)]
pub struct Int(*mut ());

impl Int {
    #[trusted]
    #[logic]
    #[open(self)]
    #[creusot::builtins = "int.Power.power"]
    pub fn pow(self, _: Int) -> Int {
        absurd
    }

    #[trusted]
    #[logic]
    #[open(self)]
    #[creusot::builtins = "int.MinMax.max"]
    pub fn max(self, _: Int) -> Int {
        absurd
    }

    #[trusted]
    #[logic]
    #[open(self)]
    #[creusot::builtins = "int.MinMax.min"]
    pub fn min(self, _: Int) -> Int {
        absurd
    }

    #[trusted]
    #[logic]
    #[open(self)]
    #[creusot::builtins = "int.EuclideanDivision.div"]
    pub fn div_euclid(self, _: Int) -> Int {
        absurd
    }

    #[trusted]
    #[logic]
    #[open(self)]
    #[creusot::builtins = "int.EuclideanDivision.mod"]
    pub fn rem_euclid(self, _: Int) -> Int {
        absurd
    }

    #[logic]
    #[open]
    pub fn abs_diff(self, other: Int) -> Int {
        if self < other {
            other - self
        } else {
            self - other
        }
    }
}

#[cfg(creusot)]
impl Add<Int> for Int {
    type Output = Int;
    #[creusot::no_translate]
    #[creusot::builtins = "add_int"]
    fn add(self, _: Int) -> Self {
        panic!()
    }
}

#[cfg(creusot)]
impl Sub<Int> for Int {
    type Output = Int;
    #[creusot::no_translate]
    #[creusot::builtins = "sub_int"]
    fn sub(self, _: Int) -> Self {
        panic!()
    }
}

#[cfg(creusot)]
impl Mul<Int> for Int {
    type Output = Int;
    #[creusot::no_translate]
    #[creusot::builtins = "mul_int"]
    fn mul(self, _: Int) -> Self {
        panic!()
    }
}

#[cfg(creusot)]
impl Div<Int> for Int {
    type Output = Int;
    #[creusot::no_translate]
    #[creusot::builtins = "div_int"]
    fn div(self, _: Int) -> Self {
        panic!()
    }
}

#[cfg(creusot)]
impl Rem<Int> for Int {
    type Output = Int;
    #[creusot::no_translate]
    #[creusot::builtins = "rem_int"]
    fn rem(self, _: Int) -> Self {
        panic!()
    }
}

#[cfg(creusot)]
impl Neg for Int {
    type Output = Int;
    #[creusot::no_translate]
    #[creusot::builtins = "neg_int"]
    fn neg(self) -> Self {
        panic!()
    }
}
