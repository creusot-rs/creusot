//! Definition for using orderings in Pearlite.

use crate::prelude::*;
use core::cmp::Ordering;

/// Trait for comparison operations (`<`, `>`, `<=`, `>=`) in Pearlite.
///
/// Types that implement this trait must satisfy some properties (see [`PartialOrd`] trait in Rust).
///
/// In particular, the order must be:
/// - [irreflexive](Self::irreflexive)
/// - [transitive](Self::transitive)
///
pub trait PartialOrdLogic {
    /// The logical `<` operation.
    #[logic]
    fn lt_log(self, other: Self) -> bool;

    /// The logical `>` operation.
    #[logic(open, inline, sealed)]
    fn gt_log(self, other: Self) -> bool {
        other < self
    }

    /// The logical `<=` operation.
    #[logic(open, inline)]
    fn le_log(self, other: Self) -> bool {
        pearlite! { self < other || self == other }
    }

    /// The logical `>=` operation.
    #[logic(open, inline, sealed)]
    fn ge_log(self, other: Self) -> bool {
        other <= self
    }

    #[logic(law)]
    #[ensures(!(self < self))]
    fn irreflexive(self);

    #[logic(law)]
    #[requires(x < y)]
    #[requires(y < z)]
    #[ensures(x < z)]
    fn transitive(x: Self, y: Self, z: Self);

    #[logic(law)]
    #[ensures((self <= other) == (self < other || self == other))]
    fn le_lt_log(self, other: Self);

    #[logic(open, sealed)]
    fn partial_cmp_log(self, other: Self) -> Option<Ordering> {
        if self == other {
            Some(Ordering::Equal)
        } else if self < other {
            Some(Ordering::Less)
        } else if other < self {
            Some(Ordering::Greater)
        } else {
            None
        }
    }
}

/// Types that implement this trait must have a total order ([`Ord`] trait in Rust).
#[allow(unused)]
pub trait OrdLogic: PartialOrdLogic {
    /// The order is total
    #[logic(law)]
    #[ensures(self < other || self == other || other < self)]
    fn lt_log_total(self, other: Self);

    /// The comparison operation.
    #[logic(open, sealed)]
    fn cmp_log(self, other: Self) -> Ordering {
        if self == other {
            Ordering::Equal
        } else if self < other {
            Ordering::Less
        } else {
            Ordering::Greater
        }
    }
}

/// A macro to easily implements the various `#[logic(law)]`s of [`PartialOrdLogic`].
///
/// # Usage
///
/// Simply use this macro in the trait impl:
/// ```
/// # use creusot_std::{logic::ord::{PartialOrdLogic, partial_ord_laws_impl}, prelude::*};
/// use std::cmp::Ordering;
/// struct MyInt(Int);
///
/// impl PartialOrdLogic for MyInt {
///     #[logic(open)]
///     fn lt_log(self, other: Self) -> bool { todo!() }
///
///     partial_ord_laws_impl! {}
/// }
///
/// impl OrdLogic for MyInt {
///     #[logic(law)]
///     #[ensures(self < other || self == other || other < self)]
///     fn lt_log_total(self, other: Self) {}
/// }
/// ```
///
/// Additionally, you can define instructions that will be injected in every generated
/// law's body. This can be useful to apply a lemma to every law:
///
/// ```
/// # use creusot_std::{logic::ord::{PartialOrdLogic, partial_ord_laws_impl}, prelude::*};
/// #[opaque]
/// pub struct MyInt(());
///
/// impl View for MyInt {
///     type ViewTy = Int;
///     #[logic(opaque)] fn view(self) -> Int { dead }
/// }
///
/// impl MyInt {
///     #[trusted]
///     #[logic]
///     #[ensures(self@ == other@ ==> self == other)]
///     fn view_inj(self, other: Self) {}
/// }
///
/// impl PartialOrdLogic for MyInt {
///     #[logic(open)]
///     fn lt_log(self, other: Self) -> bool { todo!() }
///
///     partial_ord_laws_impl! { let _ = MyInt::view_inj; }
/// }
/// ```
#[macro_export]
macro_rules! partial_ord_laws_impl {
    ( $($lemma:stmt)* ) => {
        #[::creusot_std::macros::logic(law)]
        #[::creusot_std::macros::ensures(!(self < self))]
        fn irreflexive(self) {
            $($lemma)*
        }

        #[::creusot_std::macros::logic(law)]
        #[::creusot_std::macros::requires(x < y)]
        #[::creusot_std::macros::requires(y < z)]
        #[::creusot_std::macros::ensures(x < z)]
        fn transitive(x: Self, y: Self, z: Self) {
            $($lemma)*
        }

        #[::creusot_std::macros::logic(law)]
        #[::creusot_std::macros::ensures((self <= other) == (self < other || self == other))]
        fn le_lt_log(self, other: Self) {
            $($lemma)*
        }
    };
}

pub use partial_ord_laws_impl;

impl<T: PartialOrdLogic> PartialOrdLogic for &T {
    #[logic(open, inline)]
    fn lt_log(self, other: Self) -> bool {
        *self < *other
    }

    #[logic(open, inline)]
    fn le_log(self, other: Self) -> bool {
        *self <= *other
    }

    partial_ord_laws_impl! {}
}

impl<T: OrdLogic> OrdLogic for &T {
    #[logic]
    #[ensures(self < other || self == other || other < self)]
    fn lt_log_total(self, other: Self) {
        let _ = T::lt_log_total;
    }
}

impl PartialOrdLogic for Int {
    #[logic]
    #[builtin("int.Int.(<=)")]
    fn le_log(self, _: Self) -> bool {
        dead
    }

    #[logic]
    #[builtin("int.Int.(<)")]
    fn lt_log(self, _: Self) -> bool {
        dead
    }

    #[logic]
    #[ensures(!(self < self))]
    fn irreflexive(self) {}

    #[logic]
    #[requires(x < y)]
    #[requires(y < z)]
    #[ensures(x < z)]
    fn transitive(x: Self, y: Self, z: Self) {}

    #[logic]
    #[ensures((self <= other) == (self < other || self == other))]
    fn le_lt_log(self, other: Self) {}
}

impl OrdLogic for Int {
    #[logic]
    #[ensures(self < other || self == other || other < self)]
    fn lt_log_total(self, other: Self) {}
}

macro_rules! ord_logic_impl {
    ($t:ty, $module:literal) => {
        impl PartialOrdLogic for $t {
            #[logic]
            #[builtin(concat!($module, ".le"))]
            fn le_log(self, _: Self) -> bool {
                dead
            }

            #[logic]
            #[builtin(concat!($module, ".lt"))]
            fn lt_log(self, _: Self) -> bool {
                dead
            }

            #[logic]
            #[ensures(!(self < self))]
            fn irreflexive(self) {}

            #[logic]
            #[requires(x < y)]
            #[requires(y < z)]
            #[ensures(x < z)]
            fn transitive(x: Self, y: Self, z: Self) {}

            #[logic]
            #[ensures((self <= other) == (self < other || self == other))]
            fn le_lt_log(self, other: Self) {}
        }

        impl OrdLogic for $t {
            #[logic]
            #[ensures(self < other || self == other || other < self)]
            fn lt_log_total(self, other: Self) {}
        }
    };
}

impl PartialOrdLogic for f32 {
    /// Note: the implementation of `f32::le_log` is not the `<=` operator in Rust,
    /// because it is reflexive.
    #[logic]
    #[builtin("creusot.float.Float32.lt")]
    fn lt_log(self, _: Self) -> bool {
        dead
    }

    #[logic]
    #[ensures(!(self < self))]
    fn irreflexive(self) {}

    #[logic]
    #[requires(x < y)]
    #[requires(y < z)]
    #[ensures(x < z)]
    fn transitive(x: Self, y: Self, z: Self) {}

    #[logic]
    #[ensures((self <= other) == (self < other || self == other))]
    fn le_lt_log(self, other: Self) {}
}

impl PartialOrdLogic for f64 {
    /// Note: the implementation of `f64::le_log` is not the `<=` operator in Rust,
    /// because it is reflexive.
    #[logic]
    #[builtin("creusot.float.Float64.lt")]
    fn lt_log(self, _: Self) -> bool {
        dead
    }

    #[logic]
    #[ensures(!(self < self))]
    fn irreflexive(self) {}

    #[logic]
    #[requires(x < y)]
    #[requires(y < z)]
    #[ensures(x < z)]
    fn transitive(x: Self, y: Self, z: Self) {}

    #[logic]
    #[ensures((self <= other) == (self < other || self == other))]
    fn le_lt_log(self, other: Self) {}
}

ord_logic_impl!(u8, "creusot.int.UInt8$BW$");
ord_logic_impl!(u16, "creusot.int.UInt16$BW$");
ord_logic_impl!(u32, "creusot.int.UInt32$BW$");
ord_logic_impl!(u64, "creusot.int.UInt64$BW$");
ord_logic_impl!(u128, "creusot.int.UInt128$BW$");
#[cfg(target_pointer_width = "64")]
ord_logic_impl!(usize, "creusot.int.UInt64$BW$");
#[cfg(target_pointer_width = "32")]
ord_logic_impl!(usize, "creusot.int.UInt32$BW$");
#[cfg(target_pointer_width = "16")]
ord_logic_impl!(usize, "creusot.int.UInt16$BW$");

ord_logic_impl!(i8, "creusot.int.Int8$BW$");
ord_logic_impl!(i16, "creusot.int.Int16$BW$");
ord_logic_impl!(i32, "creusot.int.Int32$BW$");
ord_logic_impl!(i64, "creusot.int.Int64$BW$");
ord_logic_impl!(i128, "creusot.int.Int128$BW$");
#[cfg(target_pointer_width = "64")]
ord_logic_impl!(isize, "creusot.int.Int64$BW$");
#[cfg(target_pointer_width = "32")]
ord_logic_impl!(isize, "creusot.int.Int32$BW$");
#[cfg(target_pointer_width = "16")]
ord_logic_impl!(isize, "creusot.int.Int16$BW$");

ord_logic_impl!(char, "creusot.prelude.Char");
ord_logic_impl!(bool, "creusot.prelude.Bool");

impl<A: PartialOrdLogic, B: PartialOrdLogic> PartialOrdLogic for (A, B) {
    #[logic(open)]
    fn lt_log(self, o: Self) -> bool {
        self.0 == o.0 && self.1 < o.1 || self.0 < o.0
    }

    #[logic(open)]
    fn le_log(self, o: Self) -> bool {
        self.0 == o.0 && self.1 <= o.1 || self.0 < o.0
    }

    partial_ord_laws_impl! {}
}
