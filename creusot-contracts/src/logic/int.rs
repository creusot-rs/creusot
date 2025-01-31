use crate::{
    logic::ops::{AddLogic, DivLogic, MulLogic, NegLogic, RemLogic, SubLogic},
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
    #[allow(unused_variables)]
    pub fn new(value: i128) -> GhostBox<Self> {
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
    #[allow(unused_variables)]
    pub fn pow(self, p: Int) -> Int {
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
    #[allow(unused_variables)]
    pub fn max(self, x: Int) -> Int {
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
    #[allow(unused_variables)]
    pub fn min(self, x: Int) -> Int {
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
    #[allow(unused_variables)]
    pub fn div_euclid(self, d: Int) -> Int {
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
    #[allow(unused_variables)]
    pub fn rem_euclid(self, d: Int) -> Int {
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

impl AddLogic for Int {
    type Output = Self;
    #[logic]
    #[trusted]
    #[creusot::no_translate]
    #[creusot::builtins = "add_int"]
    #[allow(unused_variables)]
    fn add(self, other: Self) -> Self {
        dead
    }
}

impl SubLogic for Int {
    type Output = Self;
    #[logic]
    #[trusted]
    #[creusot::no_translate]
    #[creusot::builtins = "sub_int"]
    #[allow(unused_variables)]
    fn sub(self, other: Self) -> Self {
        dead
    }
}

impl MulLogic for Int {
    type Output = Self;
    #[logic]
    #[trusted]
    #[creusot::no_translate]
    #[creusot::builtins = "mul_int"]
    #[allow(unused_variables)]
    fn mul(self, other: Self) -> Self {
        dead
    }
}

impl DivLogic for Int {
    type Output = Self;
    #[logic]
    #[trusted]
    #[creusot::no_translate]
    #[creusot::builtins = "div_int"]
    #[allow(unused_variables)]
    fn div(self, other: Self) -> Self {
        dead
    }
}

impl RemLogic for Int {
    type Output = Self;
    #[logic]
    #[trusted]
    #[creusot::no_translate]
    #[creusot::builtins = "rem_int"]
    #[allow(unused_variables)]
    fn rem(self, other: Self) -> Self {
        dead
    }
}

impl NegLogic for Int {
    type Output = Self;
    #[logic]
    #[trusted]
    #[creusot::no_translate]
    #[creusot::builtins = "neg_int"]
    fn neg(self) -> Self {
        dead
    }
}

// ========== Ghost operations =============

impl PartialEq for Int {
    #[trusted]
    #[pure]
    #[ensures(result == (*self == *other))]
    #[allow(unused_variables)]
    fn eq(&self, other: &Self) -> bool {
        unreachable!("BUG: called ghost function in normal code")
    }
}

impl Add for Int {
    type Output = Int;
    #[trusted]
    #[pure]
    #[ensures(result == self + other)]
    #[allow(unused_variables)]
    fn add(self, other: Int) -> Self {
        unreachable!("BUG: called ghost function in normal code")
    }
}

impl Sub for Int {
    type Output = Int;
    #[trusted]
    #[pure]
    #[ensures(result == self - other)]
    #[allow(unused_variables)]
    fn sub(self, other: Int) -> Self {
        unreachable!("BUG: called ghost function in normal code")
    }
}

impl Mul for Int {
    type Output = Int;
    #[trusted]
    #[pure]
    #[ensures(result == self * other)]
    #[allow(unused_variables)]
    fn mul(self, other: Int) -> Self {
        unreachable!("BUG: called ghost function in normal code")
    }
}

impl Div for Int {
    type Output = Int;
    #[trusted]
    #[pure]
    #[ensures(result == self / other)]
    #[allow(unused_variables)]
    fn div(self, other: Int) -> Self {
        unreachable!("BUG: called ghost function in normal code")
    }
}

impl Rem for Int {
    type Output = Int;
    #[trusted]
    #[pure]
    #[ensures(result == self % other)]
    #[allow(unused_variables)]
    fn rem(self, other: Int) -> Self {
        unreachable!("BUG: called ghost function in normal code")
    }
}

impl Neg for Int {
    type Output = Int;
    #[trusted]
    #[pure]
    #[ensures(result == -self)]
    fn neg(self) -> Self {
        unreachable!("BUG: called ghost function in normal code")
    }
}
