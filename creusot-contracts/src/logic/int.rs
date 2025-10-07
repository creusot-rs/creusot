use crate::{
    ghost::Plain,
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
#[intrinsic("int")]
#[builtin("int")]
pub struct Int;

impl Clone for Int {
    #[check(ghost)]
    #[ensures(result == *self)]
    fn clone(&self) -> Self {
        *self
    }
}
impl Copy for Int {}
#[trusted]
impl Plain for Int {}

// Logical functions
impl Int {
    /// Compute `self^p`.
    ///
    /// # Example
    ///
    /// ```
    /// # use creusot_contracts::*;
    /// proof_assert!(3.pow(4) == 729);
    /// ```
    #[logic]
    #[builtin("int.Power.power")]
    #[allow(unused_variables)]
    pub fn pow(self, p: Int) -> Int {
        dead
    }

    /// Compute `2^p`.
    ///
    /// # Example
    ///
    /// ```
    /// # use creusot_contracts::*;
    /// proof_assert!(pow2(4) == 16);
    /// ```
    #[logic]
    #[builtin("bv.Pow2int.pow2")]
    #[allow(unused_variables)]
    pub fn pow2(self) -> Int {
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
    #[logic]
    #[builtin("int.MinMax.max")]
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
    #[builtin("int.MinMax.min")]
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
    #[logic]
    #[builtin("int.EuclideanDivision.div")]
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
    #[logic]
    #[builtin("int.EuclideanDivision.mod")]
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
    #[logic(open)]
    pub fn abs_diff(self, other: Int) -> Int {
        if self < other { other - self } else { self - other }
    }
}

impl AddLogic for Int {
    type Output = Self;
    #[logic]
    #[builtin("mach.int.Int.(+)")]
    #[allow(unused_variables)]
    fn add(self, other: Self) -> Self {
        dead
    }
}

impl SubLogic for Int {
    type Output = Self;
    #[logic]
    #[builtin("mach.int.Int.(-)")]
    #[allow(unused_variables)]
    fn sub(self, other: Self) -> Self {
        dead
    }
}

impl MulLogic for Int {
    type Output = Self;
    #[logic]
    #[builtin("mach.int.Int.(*)")]
    #[allow(unused_variables)]
    fn mul(self, other: Self) -> Self {
        dead
    }
}

impl DivLogic for Int {
    type Output = Self;
    #[logic]
    #[builtin("mach.int.Int.div")]
    #[allow(unused_variables)]
    fn div(self, other: Self) -> Self {
        dead
    }
}

impl RemLogic for Int {
    type Output = Self;
    #[logic]
    #[builtin("mach.int.Int.mod")]
    #[allow(unused_variables)]
    fn rem(self, other: Self) -> Self {
        dead
    }
}

impl NegLogic for Int {
    type Output = Self;
    #[logic]
    #[builtin("mach.int.Int.(-_)")]
    fn neg(self) -> Self {
        dead
    }
}

// ========== Ghost operations =============

// Ghost functions
impl Int {
    /// Create a new `Int` value
    ///
    /// The result is wrapped in a [`Ghost`], so that it can only be access inside a
    /// [`ghost!`] block.
    ///
    /// You should not have to use this method directly: instead, use the `int` suffix
    /// inside of a `ghost` block:
    /// ```
    /// # use creusot_contracts::*;
    /// let x: Ghost<Int> = ghost!(1int);
    /// ghost! {
    ///     let y: Int = 2int;
    /// };
    /// ```
    #[trusted]
    #[check(ghost)]
    #[ensures(*result == value@)]
    #[allow(unreachable_code)]
    #[allow(unused_variables)]
    pub fn new(value: i128) -> Ghost<Self> {
        Ghost::conjure()
    }

    #[trusted]
    #[check(ghost)]
    #[ensures(^self == *self + 1)]
    pub fn incr_ghost(&mut self) {}

    #[trusted]
    #[check(ghost)]
    #[ensures(^self == *self - 1)]
    pub fn decr_ghost(&mut self) {}
}

impl PartialEq for Int {
    #[trusted]
    #[check(ghost)]
    #[ensures(result == (*self == *other))]
    #[allow(unused_variables)]
    fn eq(&self, other: &Self) -> bool {
        panic!()
    }
}

impl PartialOrd for Int {
    #[trusted]
    #[check(ghost)]
    #[ensures(result == Some((*self).cmp_log(*other)))]
    #[allow(unused_variables)]
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        panic!()
    }

    #[trusted]
    #[check(ghost)]
    #[ensures(result == (*self).lt_log(*other))]
    #[allow(unused_variables)]
    fn lt(&self, other: &Self) -> bool {
        panic!()
    }

    #[trusted]
    #[check(ghost)]
    #[ensures(result == (*self).le_log(*other))]
    #[allow(unused_variables)]
    fn le(&self, other: &Self) -> bool {
        panic!()
    }

    #[trusted]
    #[check(ghost)]
    #[ensures(result == (*self).gt_log(*other))]
    #[allow(unused_variables)]
    fn gt(&self, other: &Self) -> bool {
        panic!()
    }

    #[trusted]
    #[check(ghost)]
    #[ensures(result == (*self).ge_log(*other))]
    #[allow(unused_variables)]
    fn ge(&self, other: &Self) -> bool {
        panic!()
    }
}

impl Add for Int {
    type Output = Int;
    #[trusted]
    #[check(ghost)]
    #[ensures(result == self + other)]
    #[allow(unused_variables)]
    fn add(self, other: Int) -> Self {
        panic!()
    }
}

impl Sub for Int {
    type Output = Int;
    #[trusted]
    #[check(ghost)]
    #[ensures(result == self - other)]
    #[allow(unused_variables)]
    fn sub(self, other: Int) -> Self {
        panic!()
    }
}

impl Mul for Int {
    type Output = Int;
    #[trusted]
    #[check(ghost)]
    #[ensures(result == self * other)]
    #[allow(unused_variables)]
    fn mul(self, other: Int) -> Self {
        panic!()
    }
}

impl Div for Int {
    type Output = Int;
    #[trusted]
    #[check(ghost)]
    #[ensures(result == self / other)]
    #[allow(unused_variables)]
    fn div(self, other: Int) -> Self {
        panic!()
    }
}

impl Rem for Int {
    type Output = Int;
    #[trusted]
    #[check(ghost)]
    #[ensures(result == self % other)]
    #[allow(unused_variables)]
    fn rem(self, other: Int) -> Self {
        panic!()
    }
}

impl Neg for Int {
    type Output = Int;
    #[trusted]
    #[check(ghost)]
    #[ensures(result == -self)]
    fn neg(self) -> Self {
        panic!()
    }
}
