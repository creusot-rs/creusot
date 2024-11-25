use crate::{std::cmp::Ordering, *};

#[allow(unused)]
pub trait OrdLogic {
    #[logic]
    fn cmp_log(self, _: Self) -> Ordering;

    #[logic]
    #[open]
    fn le_log(self, o: Self) -> bool {
        pearlite! { self.cmp_log(o) != Ordering::Greater }
    }

    #[law]
    #[ensures(x.le_log(y) == (x.cmp_log(y) != Ordering::Greater))]
    fn cmp_le_log(x: Self, y: Self);

    #[logic]
    #[open]
    fn lt_log(self, o: Self) -> bool {
        pearlite! { self.cmp_log(o) == Ordering::Less }
    }

    #[law]
    #[ensures(x.lt_log(y) == (x.cmp_log(y) == Ordering::Less))]
    fn cmp_lt_log(x: Self, y: Self);

    #[logic]
    #[open]
    fn ge_log(self, o: Self) -> bool {
        pearlite! { self.cmp_log(o) != Ordering::Less }
    }

    #[law]
    #[ensures(x.ge_log(y) == (x.cmp_log(y) != Ordering::Less))]
    fn cmp_ge_log(x: Self, y: Self);

    #[logic]
    #[open]
    fn gt_log(self, o: Self) -> bool {
        pearlite! { self.cmp_log(o) == Ordering::Greater }
    }

    #[law]
    #[ensures(x.gt_log(y) == (x.cmp_log(y) == Ordering::Greater))]
    fn cmp_gt_log(x: Self, y: Self);

    #[law]
    #[ensures(x.cmp_log(x) == Ordering::Equal)]
    fn refl(x: Self);

    #[law]
    #[requires(x.cmp_log(y) == o)]
    #[requires(y.cmp_log(z) == o)]
    #[ensures(x.cmp_log(z) == o)]
    fn trans(x: Self, y: Self, z: Self, o: Ordering);

    #[law]
    #[requires(x.cmp_log(y) == Ordering::Less)]
    #[ensures(y.cmp_log(x) == Ordering::Greater)]
    fn antisym1(x: Self, y: Self);

    #[law]
    #[requires(x.cmp_log(y) == Ordering::Greater)]
    #[ensures(y.cmp_log(x) == Ordering::Less)]
    fn antisym2(x: Self, y: Self);

    #[law]
    #[ensures((x == y) == (x.cmp_log(y) == Ordering::Equal))]
    fn eq_cmp(x: Self, y: Self);
}

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
            #[logic]
            #[creusot::builtins = "int.Int.(<=)"]
            fn le_log(self, _: Self) -> bool {
                dead
            }

            #[trusted]
            #[logic]
            // #[creusot::builtins = "int.Int.(<)"]
            #[creusot::builtins = concat!($module, ".(<)")]
            fn lt_log(self, _: Self) -> bool {
                dead
            }

            #[trusted]
            #[logic]
            #[creusot::builtins = "int.Int.(>=)"]
            fn ge_log(self, _: Self) -> bool {
                dead
            }

            #[trusted]
            #[logic]
            #[creusot::builtins = "int.Int.(>)"]
            fn gt_log(self, _: Self) -> bool {
                dead
            }

            ord_laws_impl! {}
        }
    };
}


macro_rules! ord_logic_impl_test_laurent {
    ($t:ty, $module:literal, $signed_sym:expr) => {
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
            #[creusot::builtins = concat!($module, ".", $signed_sym, "le")]
            fn le_log(self, _: Self) -> bool {
                true
            }

            #[trusted]
            #[open]
            #[logic]
            #[creusot::builtins = concat!($module, ".", $signed_sym, "lt")]
            fn lt_log(self, _: Self) -> bool {
                true
            }

            #[trusted]
            #[open]
            #[logic]
            #[creusot::builtins = concat!($module, ".", $signed_sym, "ge")]
            fn ge_log(self, _: Self) -> bool {
                true
            }

            #[trusted]
            #[open]
            #[logic]
            #[creusot::builtins = concat!($module, ".", $signed_sym, "gt")]
            fn gt_log(self, _: Self) -> bool {
                true
            }

            ord_laws_impl! {}
        }
    };
}

ord_logic_impl!(Int, "int.Int");

ord_logic_impl!(u8, "int.Int");
ord_logic_impl!(u16, "int.Int");
ord_logic_impl_test_laurent!(u32, "prelude.prelude.UInt32", "u");
ord_logic_impl!(u64, "int.Int");
ord_logic_impl!(u128, "int.Int");
ord_logic_impl!(usize, "int.Int");

ord_logic_impl!(i8, "int.Int");
ord_logic_impl!(i16, "int.Int");
ord_logic_impl!(i32, "int.Int");
ord_logic_impl!(i64, "int.Int");
ord_logic_impl!(i128, "int.Int");

#[cfg(target_pointer_width = "64")]
ord_logic_impl!(isize, "UInt64");
#[cfg(target_pointer_width = "32")]
ord_logic_impl!(isize, "UInt32");
#[cfg(target_pointer_width = "16")]
ord_logic_impl!(isize, "UInt16");

impl OrdLogic for bool {
    #[open]
    #[logic]
    fn cmp_log(self, o: Self) -> Ordering {
        match (self, o) {
            (false, false) => Ordering::Equal,
            (true, true) => Ordering::Equal,
            (false, true) => Ordering::Less,
            (true, false) => Ordering::Greater,
        }
    }

    ord_laws_impl! {}
}

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
