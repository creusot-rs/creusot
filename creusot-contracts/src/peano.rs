//! Peano integers
//!
//! Peano integers are a specialized kind of integers, that allow to increase the integer
//! without checking for overflows.
//!
//! See <https://inria.hal.science/hal-01162661v1> for reference.
//!
//! # Usage in data structures
//!
//! They are useful when specyfying a data structure, where
//! - Checking for overflows of the length is hard (and may leak to the users of the library)
//! - Overflows are impossible, because objects are always created one-by-one.
//!
//! In this case, you could use a [`PeanoInt`] to store the length.
//!
//! # Why not always use them ?
//!
//! Well, simply because you cannot add two peano integers together, at least not
//! efficiently. if you need to do usual arithmetic operations, you should use a normal
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
#[derive(Clone, Copy, Default, PartialEq, Eq)]
pub struct PeanoInt(u64);

impl DeepModel for PeanoInt {
    type DeepModelTy = Int;
    #[logic]
    #[open]
    fn deep_model(self) -> Int {
        self.view()
    }
}

impl OrdLogic for PeanoInt {
    #[logic]
    #[open]
    fn cmp_log(self, o: Self) -> Ordering {
        self.view().cmp_log(o.view())
    }
    #[logic]
    #[open]
    fn le_log(self, o: Self) -> bool {
        self.view().le_log(o.view())
    }
    #[logic]
    #[open]
    fn lt_log(self, o: Self) -> bool {
        self.view().lt_log(o.view())
    }
    #[logic]
    #[open]
    fn ge_log(self, o: Self) -> bool {
        self.view().ge_log(o.view())
    }
    #[logic]
    #[open]
    fn gt_log(self, o: Self) -> bool {
        self.view().gt_log(o.view())
    }
    ord_laws_impl! {}
}

impl View for PeanoInt {
    type ViewTy = Int;
    #[logic]
    fn view(self) -> Int {
        self.0.view()
    }
}

impl PartialOrd for PeanoInt {
    #[ensures(result == Some(self.cmp_log(*other)))]
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}
impl Ord for PeanoInt {
    #[ensures(result == self.cmp_log(*other))]
    fn cmp(&self, other: &Self) -> Ordering {
        self.0.cmp(&other.0)
    }
}

impl PeanoInt {
    /// Create a new peano integer with value `0`.
    #[pure]
    #[ensures(result@ == 0)]
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
    #[ensures((^self)@ == (*self)@ + 1)]
    pub fn incr(&mut self) {
        // Use volatile read, to avoid optimizing successive increments.
        // SAFETY: using `read_volatile` on a reference of a `Copy` object is always safe.
        let x = unsafe { std::ptr::read_volatile(&self.0) };
        self.0 = x + 1;
    }

    /// Get the underlying integer.
    #[pure]
    #[ensures(result@ == self@)]
    pub fn to_u64(self) -> u64 {
        self.0
    }

    /// Get the underlying integer.
    #[pure]
    #[trusted]
    #[ensures(result@ == self@)]
    pub fn to_i64(self) -> i64 {
        self.0 as i64
    }

    /// Get the underlying integer.
    #[pure]
    #[ensures(result@ == self@)]
    pub fn to_u128(self) -> u128 {
        self.0 as u128
    }

    /// Get the underlying integer.
    #[pure]
    #[ensures(result@ == self@)]
    pub fn to_i128(self) -> i128 {
        self.0 as i128
    }
}

impl From<PeanoInt> for u64 {
    #[ensures(result@ == val@)]
    fn from(val: PeanoInt) -> Self {
        val.to_u64()
    }
}

impl From<PeanoInt> for i64 {
    #[ensures(result@ == val@)]
    fn from(val: PeanoInt) -> Self {
        val.to_i64()
    }
}

impl From<PeanoInt> for u128 {
    #[ensures(result@ == val@)]
    fn from(val: PeanoInt) -> Self {
        val.to_u128()
    }
}

impl From<PeanoInt> for i128 {
    #[ensures(result@ == val@)]
    fn from(val: PeanoInt) -> Self {
        val.to_i128()
    }
}
