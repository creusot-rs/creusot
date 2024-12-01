use crate::{
    std::ops::{Add, Div, Mul, Neg, Rem, Sub},
    *,
};

/// An unbounded, mathematical integer.
///
/// This type cannot be only be constructed in logical or ghost code.
///
/// # Integers in pearlite
///
/// Note that in pearlite, all integer literals are of type `Int`:
/// ```
/// # use creusot_contracts::*;
/// let x = 1i32;
/// //             ↓ need to use the view operator to convert `i32` to `Int`
/// proof_assert!(x@ == 1);
/// ```
///
/// You can use the usual operators on integers: `+`, `-`, `*`, `/` and `%`.
///
/// Note that those operators are _not_ available in ghost code.
#[trusted]
#[cfg_attr(
    creusot,
    rustc_diagnostic_item = "creusot_int",
    creusot::builtins = "prelude.prelude.Int.int"
)]
#[allow(dead_code)]
pub struct Int(*mut ());

impl crate::Clone for Int {
    #[trusted]
    #[pure]
    #[ensures(result == *self)]
    fn clone(&self) -> Self {
        *self
    }
}
impl Copy for Int {}

impl Int {
    /// Create a new `Int` value
    ///
    /// The result is wrapped in a [`GhostBox`], so that it can only be access inside a
    /// [`ghost!`] block.
    ///
    /// You should not have to use this method directly: instead, use the `int` suffix
    /// inside of a `ghost` block:
    /// ```
    /// # use creusot_contracts::*;
    /// let x: GhostBox<Int> = ghost!(1int);
    /// ghost! {
    ///     let y: Int = 2int;
    /// };
    /// ```
    #[trusted]
    #[pure]
    #[ensures(*result == value@)]
    #[allow(unreachable_code)]
    pub fn new(value: i128) -> GhostBox<Self> {
        let _ = value;
        ghost!(panic!())
    }

    /// Compute `self^p`.
    ///
    /// # Example
    ///
    /// ```
    /// # use creusot_contracts::*;
    /// proof_assert!(2.pow(3) == 8);
    /// ```
    #[trusted]
    #[logic]
    #[creusot::builtins = "int.Power.power"]
    pub fn pow(self, p: Int) -> Int {
        let _ = p;
        dead
    }

    /// Compute the maximum of `self` and `x`.
    ///
    /// # Example
    ///
    /// ```
    /// # use creusot_contracts::*;
    /// proof_assert!(10.max(2) == 10);
    /// ```
    #[trusted]
    #[logic]
    #[creusot::builtins = "int.MinMax.max"]
    pub fn max(self, x: Int) -> Int {
        let _ = x;
        dead
    }

    /// Compute the minimum of `self` and `x`.
    ///
    /// # Example
    ///
    /// ```
    /// # use creusot_contracts::*;
    /// proof_assert!(10.max(2) == 2);
    /// ```
    #[logic]
    #[creusot::builtins = "int.MinMax.min"]
    #[trusted]
    pub fn min(self, x: Int) -> Int {
        let _ = x;
        dead
    }

    /// Compute the euclidean division of `self` by `d`.
    ///
    /// # Example
    ///
    /// ```
    /// # use creusot_contracts::*;
    /// proof_assert!(10.div_euclid(3) == 3);
    /// ```
    #[trusted]
    #[logic]
    #[creusot::builtins = "int.EuclideanDivision.div"]
    pub fn div_euclid(self, d: Int) -> Int {
        let _ = d;
        dead
    }

    /// Compute the remainder of the euclidean division of `self` by `d`.
    ///
    /// # Example
    ///
    /// ```
    /// # use creusot_contracts::*;
    ///  proof_assert!(10.rem_euclid(3) == 1);
    /// ```
    #[trusted]
    #[logic]
    #[creusot::builtins = "int.EuclideanDivision.mod"]
    pub fn rem_euclid(self, d: Int) -> Int {
        let _ = d;
        dead
    }

    /// Compute the absolute difference of `self` and `x`.
    ///
    /// # Example
    ///
    /// ```
    /// # use creusot_contracts::*;
    /// proof_assert!(10.abs_diff(3) == 7);
    /// proof_assert!(3.abs_diff(10) == 7);
    /// proof_assert!((-5).abs_diff(5) == 10);
    /// ```
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
    #[trusted]
    #[creusot::no_translate]
    #[creusot::builtins = "add_int"]
    fn add(self, _: Int) -> Self {
        panic!()
    }
}

#[cfg(creusot)]
impl Sub<Int> for Int {
    type Output = Int;
    #[trusted]
    #[creusot::no_translate]
    #[creusot::builtins = "sub_int"]
    fn sub(self, _: Int) -> Self {
        panic!()
    }
}

#[cfg(creusot)]
impl Mul<Int> for Int {
    type Output = Int;
    #[trusted]
    #[creusot::no_translate]
    #[creusot::builtins = "mul_int"]
    fn mul(self, _: Int) -> Self {
        panic!()
    }
}

#[cfg(creusot)]
impl Div<Int> for Int {
    type Output = Int;
    #[trusted]
    #[creusot::no_translate]
    #[creusot::builtins = "div_int"]
    fn div(self, _: Int) -> Self {
        panic!()
    }
}

#[cfg(creusot)]
impl Rem<Int> for Int {
    type Output = Int;
    #[trusted]
    #[creusot::no_translate]
    #[creusot::builtins = "rem_int"]
    fn rem(self, _: Int) -> Self {
        panic!()
    }
}

#[cfg(creusot)]
impl Neg for Int {
    type Output = Int;
    #[trusted]
    #[creusot::no_translate]
    #[creusot::builtins = "neg_int"]
    fn neg(self) -> Self {
        panic!()
    }
}
