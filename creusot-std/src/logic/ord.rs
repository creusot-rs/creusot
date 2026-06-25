//! Definition for using orderings in pearlite.

use crate::prelude::*;
use core::cmp::Ordering;

/// Trait for comparison operations (`<`, `>`, `<=`, `>=`) in pearlite.
///
/// Types that implement this trait must have a partial order ([`PartialOrd`] trait in Rust).
///
/// In particular, the order must be:
/// - [reflexive](Self::refl)
/// - [transitive](Self::trans)
/// - asymmetric ([part1](Self::antisym1), [part2](Self::antisym2))

pub trait PartialOrdLogic {
    /// The comparison operation.
    #[logic]
    fn partial_cmp_log(self, other: Self) -> Option<Ordering>;

    /// The logical `<=` operation.
    #[logic(open)]
    fn le_log(self, o: Self) -> bool {
        pearlite! { self.partial_cmp_log(o) == Some(Ordering::Less) || self.partial_cmp_log(o) == Some(Ordering::Equal) }
    }

    #[logic(law)]
    #[ensures(x.le_log(y) == (x.partial_cmp_log(y) == Some(Ordering::Less) || x.partial_cmp_log(y) == Some(Ordering::Equal)))]
    fn partial_cmp_le_log(x: Self, y: Self);

    /// The logical `<` operation.
    #[logic(open)]
    fn lt_log(self, o: Self) -> bool {
        pearlite! { self.partial_cmp_log(o) == Some(Ordering::Less) }
    }

    #[logic(law)]
    #[ensures(x.lt_log(y) == (x.partial_cmp_log(y) == Some(Ordering::Less)))]
    fn partial_cmp_lt_log(x: Self, y: Self);

    /// The logical `>=` operation.
    #[logic(open)]
    fn ge_log(self, o: Self) -> bool {
        pearlite! { self.partial_cmp_log(o) == Some(Ordering::Greater) || self.partial_cmp_log(o) == Some(Ordering::Equal) }
    }

    #[logic(law)]
    #[ensures(x.ge_log(y) == (x.partial_cmp_log(y) == Some(Ordering::Greater) || x.partial_cmp_log(y) == Some(Ordering::Equal)))]
    fn partial_cmp_ge_log(x: Self, y: Self);

    /// The logical `>` operation.
    #[logic(open)]
    fn gt_log(self, o: Self) -> bool {
        pearlite! { self.partial_cmp_log(o) == Some(Ordering::Greater) }
    }

    #[logic(law)]
    #[ensures(x.gt_log(y) == (x.partial_cmp_log(y) == Some(Ordering::Greater)))]
    fn partial_cmp_gt_log(x: Self, y: Self);

    /// The order is reflexive : a == a
    #[logic(law)]
    #[ensures(x.partial_cmp_log(x) == Some(Ordering::Equal))]
    fn refl(x: Self);

    /// The order R is transitive : a R b && b R c ==> a R c
    #[logic(law)]
    #[requires(x.partial_cmp_log(y) == o)]
    #[requires(y.partial_cmp_log(z) == o)]
    #[ensures(x.partial_cmp_log(z) == o)]
    fn trans(x: Self, y: Self, z: Self, o: Option<Ordering>);

    /// The order is asymmetric : a < b ==> !(b < a)
    ///
    /// The asymmetry is in two part; here is the [first](Self::asymetric2) part.
    #[logic(law)]
    #[requires(x.partial_cmp_log(y) == Some(Ordering::Less))]
    #[ensures(y.partial_cmp_log(x) == Some(Ordering::Greater))]
    fn asymetric1(x: Self, y: Self);

    /// The order is asymmetric : a > b ==> !(a > b)
    ///
    /// The asymmetry is in two part; here is the [second](Self::asymetric1) part.
    #[logic(law)]
    #[requires(x.partial_cmp_log(y) == Some(Ordering::Greater))]
    #[ensures(y.partial_cmp_log(x) == Some(Ordering::Less))]
    fn asymetric2(x: Self, y: Self);

    /// Compatibility between [`Ordering::Equal`] and equality (`==`).
    ///
    /// This implies irreflexivity of the order.
    #[logic(law)]
    #[ensures((x == y) == (x.partial_cmp_log(y) == Some(Ordering::Equal)))]
    fn eq_partial_cmp(x: Self, y: Self);
}

/// Types that implement this trait must have a total order ([`Ord`] trait in Rust).
#[allow(unused)]
pub trait OrdLogic: PartialOrdLogic {
    /// The comparison operation.
    #[logic(open, inline, sealed)]
    fn cmp_log(self, other: Self) -> Ordering {
        self.partial_cmp_log(other).unwrap_logic()
    }

    /// TODO
    #[logic(law)]
    #[ensures(self.partial_cmp_log(other) != None)]
    fn partial_cmp_log_total(self, other: Self);
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
///     #[logic]
///     fn partial_cmp_log(self, other: Self) -> Option<Ordering> { todo!() }
///     #[logic]
///     fn le_log(self, other: Self) -> bool { todo!() }
///     #[logic]
///     fn lt_log(self, other: Self) -> bool { todo!() }
///     #[logic]
///     fn ge_log(self, other: Self) -> bool { todo!() }
///     #[logic]
///     fn gt_log(self, other: Self) -> bool { todo!() }
///
///     partial_ord_laws_impl! {}
/// }
///
/// impl OrdLogic for MyInt {
///     #[logic]
///     #[ensures(self.partial_cmp_log(other) == Some(result))]
///     fn cmp_log(self, other: Self) -> Ordering { todo!() }
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
///     fn partial_cmp_log(self, other: Self) -> Option<Ordering> { pearlite! { self@.partial_cmp_log(other@) } }
/// #    #[logic]
/// #    fn le_log(self, other: Self) -> bool { todo!() }
/// #    #[logic]
/// #    fn lt_log(self, other: Self) -> bool { todo!() }
/// #    #[logic]
/// #    fn ge_log(self, other: Self) -> bool { todo!() }
/// #    #[logic]
/// #    fn gt_log(self, other: Self) -> bool { todo!() }
///     // ...
///
///     partial_ord_laws_impl! { let _ = MyInt::view_inj; }
/// }
/// ```
#[macro_export]
macro_rules! partial_ord_laws_impl {
    ( $($lemma:stmt)* ) => {
        #[::creusot_std::macros::logic(open(self), law)]
        #[::creusot_std::macros::ensures(x.le_log(y) == (x.partial_cmp_log(y) == core::option::Option::Some(core::cmp::Ordering::Less) || x.partial_cmp_log(y) == core::option::Option::Some(core::cmp::Ordering::Equal)))]
        fn partial_cmp_le_log(x: Self, y: Self) {
            $($lemma)*
        }

        #[::creusot_std::macros::logic(open(self), law)]
        #[::creusot_std::macros::ensures(x.lt_log(y) == (x.partial_cmp_log(y) == core::option::Option::Some(core::cmp::Ordering::Less)))]
        fn partial_cmp_lt_log(x: Self, y: Self) {
            $($lemma)*
        }

        #[::creusot_std::macros::logic(open(self), law)]
        #[::creusot_std::macros::ensures(x.ge_log(y) == (x.partial_cmp_log(y) == core::option::Option::Some(core::cmp::Ordering::Greater) || x.partial_cmp_log(y) == core::option::Option::Some(core::cmp::Ordering::Equal)))]
        fn partial_cmp_ge_log(x: Self, y: Self) {
            $($lemma)*
        }

        #[::creusot_std::macros::logic(open(self), law)]
        #[::creusot_std::macros::ensures(x.gt_log(y) == (x.partial_cmp_log(y) == core::option::Option::Some(core::cmp::Ordering::Greater)))]
        fn partial_cmp_gt_log(x: Self, y: Self) {
            $($lemma)*
        }

        #[::creusot_std::macros::logic(open(self), law)]
        #[::creusot_std::macros::ensures(x.partial_cmp_log(x) == core::option::Option::Some(core::cmp::Ordering::Equal))]
        fn refl(x: Self) {
            $($lemma)*
        }

        #[::creusot_std::macros::logic(open(self), law)]
        #[::creusot_std::macros::requires(x.partial_cmp_log(y) == o)]
        #[::creusot_std::macros::requires(y.partial_cmp_log(z) == o)]
        #[::creusot_std::macros::ensures(x.partial_cmp_log(z) == o)]
        fn trans(x: Self, y: Self, z: Self, o: core::option::Option<core::cmp::Ordering>) {
            $($lemma)*
        }

        #[::creusot_std::macros::logic(open(self), law)]
        #[::creusot_std::macros::requires(x.partial_cmp_log(y) == core::option::Option::Some(core::cmp::Ordering::Less))]
        #[::creusot_std::macros::ensures(y.partial_cmp_log(x) == core::option::Option::Some(core::cmp::Ordering::Greater))]
        fn asymetric1(x: Self, y: Self) {
            $($lemma)*
        }

        #[::creusot_std::macros::logic(open(self), law)]
        #[::creusot_std::macros::requires(x.partial_cmp_log(y) == core::option::Option::Some(core::cmp::Ordering::Greater))]
        #[::creusot_std::macros::ensures(y.partial_cmp_log(x) == core::option::Option::Some(core::cmp::Ordering::Less))]
        fn asymetric2(x: Self, y: Self) {
            $($lemma)*
        }

        #[::creusot_std::macros::logic(open(self), law)]
        #[::creusot_std::macros::ensures((x == y) == (x.partial_cmp_log(y) == core::option::Option::Some(core::cmp::Ordering::Equal)))]
        fn eq_partial_cmp(x: Self, y: Self) {
            $($lemma)*
        }
    };
}

pub use partial_ord_laws_impl;

impl<T: PartialOrdLogic> PartialOrdLogic for &T {
    #[logic(open)]
    fn partial_cmp_log(self, o: Self) -> Option<Ordering> {
        T::partial_cmp_log(*self, *o)
    }

    #[logic]
    fn le_log(self, other: Self) -> bool {
        T::le_log(*self, *other)
    }

    #[logic]
    fn lt_log(self, other: Self) -> bool {
        T::lt_log(*self, *other)
    }

    #[logic]
    fn ge_log(self, other: Self) -> bool {
        T::ge_log(*self, *other)
    }

    #[logic]
    fn gt_log(self, other: Self) -> bool {
        T::gt_log(*self, *other)
    }

    partial_ord_laws_impl! {}
}

impl<T: OrdLogic> OrdLogic for &T {
    #[logic(law)]
    #[ensures(self.partial_cmp_log(other) != None)]
    fn partial_cmp_log_total(self, other: Self) {}
}

impl PartialOrdLogic for Int {
    #[logic(open)]
    fn partial_cmp_log(self, o: Self) -> Option<Ordering> {
        if self < o {
            Some(Ordering::Less)
        } else if self == o {
            Some(Ordering::Equal)
        } else {
            Some(Ordering::Greater)
        }
    }

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
    #[builtin("int.Int.(>=)")]
    fn ge_log(self, _: Self) -> bool {
        dead
    }

    #[logic]
    #[builtin("int.Int.(>)")]
    fn gt_log(self, _: Self) -> bool {
        dead
    }

    partial_ord_laws_impl! {}
}

impl OrdLogic for Int {
    #[logic(law)]
    #[ensures(self.partial_cmp_log(other) != None)]
    fn partial_cmp_log_total(self, other: Self) {}
}

macro_rules! ord_logic_impl {
    ($t:ty, $module:literal) => {
        impl PartialOrdLogic for $t {
            #[logic(open)]
            fn partial_cmp_log(self, o: Self) -> Option<Ordering> {
                if self < o {
                    Some(Ordering::Less)
                } else if self == o {
                    Some(Ordering::Equal)
                } else {
                    Some(Ordering::Greater)
                }
            }

            #[logic]
            #[builtin(concat!($module, ".le"))]
            fn le_log(self, _: Self) -> bool {
                true
            }

            #[logic]
            #[builtin(concat!($module, ".lt"))]
            fn lt_log(self, _: Self) -> bool {
                true
            }

            #[logic]
            #[builtin(concat!($module, ".ge"))]
            fn ge_log(self, _: Self) -> bool {
                true
            }

            #[logic]
            #[builtin(concat!($module, ".gt"))]
            fn gt_log(self, _: Self) -> bool {
                true
            }

            partial_ord_laws_impl! {}
        }

        impl OrdLogic for $t {
            #[logic(law)]
            #[ensures(self.partial_cmp_log(other) != None)]
            fn partial_cmp_log_total(self, other: Self) {}
        }
    };
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
    fn partial_cmp_log(self, o: Self) -> Option<Ordering> {
        pearlite! { {
            let r = self.0.partial_cmp_log(o.0);
            if r == Some(Ordering::Equal) {
                self.1.partial_cmp_log(o.1)
            } else {
                r
            }
        } }
    }

    #[logic(open)]
    fn le_log(self, o: Self) -> bool {
        pearlite! { (self.0 == o.0 && self.1 <= o.1) || self.0 < o.0 }
    }

    #[logic(open)]
    fn lt_log(self, o: Self) -> bool {
        pearlite! { (self.0 == o.0 && self.1 < o.1) || self.0 < o.0 }
    }

    #[logic(open)]
    fn ge_log(self, o: Self) -> bool {
        pearlite! { (self.0 == o.0 && self.1 >= o.1) || self.0 > o.0 }
    }

    #[logic(open)]
    fn gt_log(self, o: Self) -> bool {
        pearlite! { (self.0 == o.0 && self.1 > o.1) || self.0 > o.0 }
    }

    partial_ord_laws_impl! {}
}
