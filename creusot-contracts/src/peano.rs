//! Peano integers
//!
//! Peano integers are a specialized kind of integers, that allow to increase the integer
//! without checking for overflows.
//!
//! See <https://inria.hal.science/hal-01162661v1> for reference.
//!
//! # Usage in data structures
//!
//! They are useful when specifying a data structure where
//! - checking for overflows of the length is hard (and may leak to the users of the library),
//! - overflows are practically impossible because the length only grows by one at a time.
//!
//! In this case, you could use a [`PeanoInt`] to store the length.
//!
//! # Why not always use them ?
//!
//! Well, simply because you cannot add two peano integers together, at least not
//! efficiently. If you need to do usual arithmetic operations, you should use a normal
//! integer.
//!
//! # Ghost code
//!
//! You cannot increase a peano integer in [ghost](macro@crate::ghost) code, as it may
//! overflow the backing integer. Since ghost code is not executed, the time argument is
//! not applicable.

use crate::{Clone, Default, PartialEq, *};
use ::std::cmp::Ordering;

/// A peano integer wrapping a 64-bits integer.
///
/// See the [module](crate::peano) explanation.
#[derive(Clone, Copy, Default, Eq)]
#[non_exhaustive]
#[repr(transparent)]
pub struct PeanoInt(pub u64);

impl DeepModel for PeanoInt {
    type DeepModelTy = u64;
    #[logic]
    #[open]
    fn deep_model(self) -> u64 {
        self.0
    }
}

impl OrdLogic for PeanoInt {
    #[logic]
    #[open]
    fn cmp_log(self, o: Self) -> Ordering {
        self.0.cmp_log(o.0)
    }
    #[logic]
    #[open]
    fn le_log(self, o: Self) -> bool {
        self.0.le_log(o.0)
    }
    #[logic]
    #[open]
    fn lt_log(self, o: Self) -> bool {
        self.0.lt_log(o.0)
    }
    #[logic]
    #[open]
    fn ge_log(self, o: Self) -> bool {
        self.0.ge_log(o.0)
    }
    #[logic]
    #[open]
    fn gt_log(self, o: Self) -> bool {
        self.0.gt_log(o.0)
    }
    ord_laws_impl! {}
}

impl View for PeanoInt {
    type ViewTy = u64;
    #[logic]
    #[open]
    fn view(self) -> u64 {
        self.0
    }
}

impl PartialOrd for PeanoInt {
    #[check(ghost)]
    #[ensures(result == Some((*self).cmp_log(*other)))]
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}
impl Ord for PeanoInt {
    #[check(ghost)]
    #[ensures(result == (*self).cmp_log(*other))]
    fn cmp(&self, other: &Self) -> Ordering {
        self.0.cmp(&other.0)
    }
}
impl PartialEq for PeanoInt {
    #[check(ghost)]
    #[ensures(result == (*self == *other))]
    fn eq(&self, other: &Self) -> bool {
        self.0 == other.0
    }
}

impl PeanoInt {
    /// Create a new peano integer with value `0`.
    #[check(ghost)]
    #[ensures(result.0 == 0u64)]
    pub fn new() -> Self {
        Self(0)
    }

    /// Increase the integer by one.
    ///
    /// This method guarantees that increments cannot get optimized together, e.g. that
    /// ```rust
    /// # use creusot_contracts::peano::PeanoInt;
    /// let mut x = PeanoInt::new();
    /// for _ in 0..1_000_000 {
    ///     x.incr();
    /// }
    /// ```
    /// Does not get optimized down to a single addition.
    ///
    /// Since the backing integer is 64 bits long, no program could ever actually reach
    /// the point where the integer overflows.
    #[trusted]
    #[check(terminates)]
    #[ensures(result.0@ == self.0@ + 1)]
    pub fn incr(self) -> Self {
        // Use volatile read, to avoid optimizing successive increments.
        // SAFETY: using `read_volatile` on a reference of a `Copy` object is always safe.
        let x = unsafe { std::ptr::read_volatile(&self.0) };
        Self(x + 1)
    }

    /// Get the underlying integer.
    #[check(ghost)]
    #[ensures(result == self.0)]
    pub fn to_u64(self) -> u64 {
        self.0
    }

    /// Get the underlying integer.
    #[check(ghost)]
    #[trusted]
    #[ensures(result@ == self.0@)]
    pub fn to_i64(self) -> i64 {
        self.0 as i64
    }

    /// Get the underlying integer.
    #[check(ghost)]
    #[ensures(result@ == self.0@)]
    pub fn to_u128(self) -> u128 {
        self.0 as u128
    }

    /// Get the underlying integer.
    #[check(ghost)]
    #[ensures(result@ == self.0@)]
    pub fn to_i128(self) -> i128 {
        self.0 as i128
    }
}

impl From<PeanoInt> for u64 {
    #[check(ghost)]
    #[ensures(result == val.0)]
    fn from(val: PeanoInt) -> Self {
        val.to_u64()
    }
}

impl From<PeanoInt> for i64 {
    #[check(ghost)]
    #[ensures(result@ == val.0@)]
    fn from(val: PeanoInt) -> Self {
        val.to_i64()
    }
}

impl From<PeanoInt> for u128 {
    #[check(ghost)]
    #[ensures(result@ == val.0@)]
    fn from(val: PeanoInt) -> Self {
        val.to_u128()
    }
}

impl From<PeanoInt> for i128 {
    #[check(ghost)]
    #[ensures(result@ == val.0@)]
    fn from(val: PeanoInt) -> Self {
        val.to_i128()
    }
}
