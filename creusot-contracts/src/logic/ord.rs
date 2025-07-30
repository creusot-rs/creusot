//! Definition for using orderings in pearlite.

use crate::{std::cmp::Ordering, *};

/// Trait for comparison operations (`<`, `>`, `<=`, `>=`) in pearlite.
///
/// Types that implement this trait must have a total order. In particular, the order
/// must be:
/// - [reflexive](Self::refl)
/// - [transitive](Self::trans)
/// - antisymmetric ([part1](Self::antisym1), [part2](Self::antisym2))
#[allow(unused)]
pub trait OrdLogic {
    /// The comparison operation. Returns:
    /// - [`Ordering::Less`] if `self` is smaller than `other`
    /// - [`Ordering::Equal`] if `self` is equal to `other`
    /// - [`Ordering::Greater`] if `self` is greater than `other`
    #[logic]
    fn cmp_log(self, other: Self) -> Ordering;

    /// The logical `<=` operation.
    #[logic]
    #[open]
    fn le_log(self, o: Self) -> bool {
        pearlite! { self.cmp_log(o) != Ordering::Greater }
    }

    #[law]
    #[ensures(x.le_log(y) == (x.cmp_log(y) != Ordering::Greater))]
    fn cmp_le_log(x: Self, y: Self);

    /// The logical `<` operation.
    #[logic]
    #[open]
    fn lt_log(self, o: Self) -> bool {
        pearlite! { self.cmp_log(o) == Ordering::Less }
    }

    #[law]
    #[ensures(x.lt_log(y) == (x.cmp_log(y) == Ordering::Less))]
    fn cmp_lt_log(x: Self, y: Self);

    /// The logical `>=` operation.
    #[logic]
    #[open]
    fn ge_log(self, o: Self) -> bool {
        pearlite! { self.cmp_log(o) != Ordering::Less }
    }

    #[law]
    #[ensures(x.ge_log(y) == (x.cmp_log(y) != Ordering::Less))]
    fn cmp_ge_log(x: Self, y: Self);

    /// The logical `>` operation.
    #[logic]
    #[open]
    fn gt_log(self, o: Self) -> bool {
        pearlite! { self.cmp_log(o) == Ordering::Greater }
    }

    #[law]
    #[ensures(x.gt_log(y) == (x.cmp_log(y) == Ordering::Greater))]
    fn cmp_gt_log(x: Self, y: Self);

    /// Reflexivity of the order
    #[law]
    #[ensures(x.cmp_log(x) == Ordering::Equal)]
    fn refl(x: Self);

    /// Transitivity of the order
    #[law]
    #[requires(x.cmp_log(y) == o)]
    #[requires(y.cmp_log(z) == o)]
    #[ensures(x.cmp_log(z) == o)]
    fn trans(x: Self, y: Self, z: Self, o: Ordering);

    /// Antisymmetry of the order (`x < y ==> !(y < x)`)
    ///
    /// The antisymmetry is in two part; here is the [second](Self::antisym2) part.
    #[law]
    #[requires(x.cmp_log(y) == Ordering::Less)]
    #[ensures(y.cmp_log(x) == Ordering::Greater)]
    fn antisym1(x: Self, y: Self);

    /// Antisymmetry of the order (`x > y ==> !(y > x)`)
    ///
    /// The antisymmetry is in two part; here is the [first](Self::antisym1) part.
    #[law]
    #[requires(x.cmp_log(y) == Ordering::Greater)]
    #[ensures(y.cmp_log(x) == Ordering::Less)]
    fn antisym2(x: Self, y: Self);

    /// Compatibility between [`Ordering::Equal`] and equality (`==`).
    #[law]
    #[ensures((x == y) == (x.cmp_log(y) == Ordering::Equal))]
    fn eq_cmp(x: Self, y: Self);
}

/// A macro to easily implements the various `#[law]`s of [`OrdLogic`].
///
/// # Usage
///
/// Simply use this macro in the trait impl:
/// ```
/// # use creusot_contracts::{logic::ord::{OrdLogic, ord_laws_impl}, *};
/// use ::std::cmp::Ordering;
/// struct MyInt(Int);
///
/// impl OrdLogic for MyInt {
///     #[logic]
///     fn cmp_log(self, other: Self) -> Ordering { todo!() }
///     #[logic]
///     fn le_log(self, other: Self) -> bool { todo!() }
///     #[logic]
///     fn lt_log(self, other: Self) -> bool { todo!() }
///     #[logic]
///     fn ge_log(self, other: Self) -> bool { todo!() }
///     #[logic]
///     fn gt_log(self, other: Self) -> bool { todo!() }
///
///     ord_laws_impl! {}
/// }
/// ```
#[macro_export]
macro_rules! ord_laws_impl {
    () => {
        #[::creusot_contracts::law]
        #[::creusot_contracts::open(self)]
        #[::creusot_contracts::ensures(x.le_log(y) == (x.cmp_log(y) != Ordering::Greater))]
        fn cmp_le_log(x: Self, y: Self) {}

        #[::creusot_contracts::law]
        #[::creusot_contracts::open(self)]
        #[::creusot_contracts::ensures(x.lt_log(y) == (x.cmp_log(y) == Ordering::Less))]
        fn cmp_lt_log(x: Self, y: Self) {}

        #[::creusot_contracts::law]
        #[::creusot_contracts::open(self)]
        #[::creusot_contracts::ensures(x.ge_log(y) == (x.cmp_log(y) != Ordering::Less))]
        fn cmp_ge_log(x: Self, y: Self) {}

        #[::creusot_contracts::law]
        #[::creusot_contracts::open(self)]
        #[::creusot_contracts::ensures(x.gt_log(y) == (x.cmp_log(y) == Ordering::Greater))]
        fn cmp_gt_log(x: Self, y: Self) {}

        #[::creusot_contracts::law]
        #[::creusot_contracts::open(self)]
        #[::creusot_contracts::ensures(x.cmp_log(x) == Ordering::Equal)]
        fn refl(x: Self) {}

        #[::creusot_contracts::law]
        #[::creusot_contracts::open(self)]
        #[::creusot_contracts::requires(x.cmp_log(y) == o)]
        #[::creusot_contracts::requires(y.cmp_log(z) == o)]
        #[::creusot_contracts::ensures(x.cmp_log(z) == o)]
        fn trans(x: Self, y: Self, z: Self, o: Ordering) {}

        #[::creusot_contracts::law]
        #[::creusot_contracts::open(self)]
        #[::creusot_contracts::requires(x.cmp_log(y) == Ordering::Less)]
        #[::creusot_contracts::ensures(y.cmp_log(x) == Ordering::Greater)]
        fn antisym1(x: Self, y: Self) {}

        #[::creusot_contracts::law]
        #[::creusot_contracts::open(self)]
        #[::creusot_contracts::requires(x.cmp_log(y) == Ordering::Greater)]
        #[::creusot_contracts::ensures(y.cmp_log(x) == Ordering::Less)]
        fn antisym2(x: Self, y: Self) {}

        #[::creusot_contracts::law]
        #[::creusot_contracts::open(self)]
        #[::creusot_contracts::ensures((x == y) == (x.cmp_log(y) == Ordering::Equal))]
        fn eq_cmp(x: Self, y: Self) {}
    };
}

pub use ord_laws_impl;

impl OrdLogic for Int {
    #[logic]
    #[open]
    fn cmp_log(self, o: Self) -> Ordering {
        if self < o {
            Ordering::Less
        } else if self == o {
            Ordering::Equal
        } else {
            Ordering::Greater
        }
    }

    #[trusted]
    #[logic]
    #[creusot::builtins = "mach.int.Int.(<=)"]
    fn le_log(self, _: Self) -> bool {
        dead
    }

    #[trusted]
    #[logic]
    #[creusot::builtins = "mach.int.Int.(<)"]
    fn lt_log(self, _: Self) -> bool {
        dead
    }

    #[trusted]
    #[logic]
    #[creusot::builtins = "mach.int.Int.(>=)"]
    fn ge_log(self, _: Self) -> bool {
        dead
    }

    #[trusted]
    #[logic]
    #[creusot::builtins = "mach.int.Int.(>)"]
    fn gt_log(self, _: Self) -> bool {
        dead
    }

    ord_laws_impl! {}
}

macro_rules! ord_logic_impl {
    ($t:ty, $module:literal) => {
        impl OrdLogic for $t {
            #[logic]
            #[open]
            fn cmp_log(self, o: Self) -> Ordering {
                if self < o {
                    Ordering::Less
                } else if self == o {
                    Ordering::Equal
                } else {
                    Ordering::Greater
                }
            }

            #[trusted]
            #[open]
            #[logic]
            #[creusot::builtins = concat!($module, ".le")]
            fn le_log(self, _: Self) -> bool {
                true
            }

            #[trusted]
            #[open]
            #[logic]
            #[creusot::builtins = concat!($module, ".lt")]
            fn lt_log(self, _: Self) -> bool {
                true
            }

            #[trusted]
            #[open]
            #[logic]
            #[creusot::builtins = concat!($module, ".ge")]
            fn ge_log(self, _: Self) -> bool {
                true
            }

            #[trusted]
            #[open]
            #[logic]
            #[creusot::builtins = concat!($module, ".gt")]
            fn gt_log(self, _: Self) -> bool {
                true
            }

            ord_laws_impl! {}
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

impl<A: OrdLogic, B: OrdLogic> OrdLogic for (A, B) {
    #[logic]
    #[open]
    fn cmp_log(self, o: Self) -> Ordering {
        pearlite! { {
            let r = self.0.cmp_log(o.0);
            if r == Ordering::Equal {
                self.1.cmp_log(o.1)
            } else {
                r
            }
        } }
    }

    #[logic]
    #[open]
    fn le_log(self, o: Self) -> bool {
        pearlite! { (self.0 == o.0 && self.1 <= o.1) || self.0 < o.0 }
    }

    #[logic]
    #[open]
    fn lt_log(self, o: Self) -> bool {
        pearlite! { (self.0 == o.0 && self.1 < o.1) || self.0 < o.0 }
    }

    #[logic]
    #[open]
    fn ge_log(self, o: Self) -> bool {
        pearlite! { (self.0 == o.0 && self.1 >= o.1) || self.0 > o.0 }
    }

    #[logic]
    #[open]
    fn gt_log(self, o: Self) -> bool {
        pearlite! { (self.0 == o.0 && self.1 > o.1) || self.0 > o.0 }
    }

    ord_laws_impl! {}
}
