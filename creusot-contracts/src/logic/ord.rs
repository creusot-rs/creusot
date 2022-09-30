use crate as creusot_contracts;
// use crate::logic::EqLogic;
use crate::{logic::Int, macros::*};
pub use std::cmp::Ordering;

#[allow(unused)]
pub trait OrdLogic {
    #[logic]
    fn cmp_log(self, _: Self) -> Ordering;

    #[predicate]
    fn le_log(self, o: Self) -> bool {
        pearlite! { self.cmp_log(o) != Ordering::Greater }
    }

    #[law]
    #[ensures(x.le_log(y) == (x.cmp_log(y) != Ordering::Greater))]
    fn cmp_le_log(x: Self, y: Self);

    #[predicate]
    fn lt_log(self, o: Self) -> bool {
        pearlite! { self.cmp_log(o) == Ordering::Less }
    }

    #[law]
    #[ensures(x.lt_log(y) == (x.cmp_log(y) == Ordering::Less))]
    fn cmp_lt_log(x: Self, y: Self);

    #[predicate]
    fn ge_log(self, o: Self) -> bool {
        pearlite! { self.cmp_log(o) != Ordering::Less }
    }

    #[law]
    #[ensures(x.ge_log(y) == (x.cmp_log(y) != Ordering::Less))]
    fn cmp_ge_log(x: Self, y: Self);

    #[predicate]
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

macro_rules! ord_logic_impl {
    ($t:ty) => {
        impl OrdLogic for $t {
            #[logic]
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
            #[predicate]
            #[creusot::builtins = "int.Int.(<=)"]
            fn le_log(self, _: Self) -> bool {
                true
            }

            #[trusted]
            #[predicate]
            #[creusot::builtins = "int.Int.(<)"]
            fn lt_log(self, _: Self) -> bool {
                true
            }

            #[trusted]
            #[predicate]
            #[creusot::builtins = "int.Int.(>=)"]
            fn ge_log(self, _: Self) -> bool {
                true
            }

            #[trusted]
            #[predicate]
            #[creusot::builtins = "int.Int.(>)"]
            fn gt_log(self, _: Self) -> bool {
                true
            }

            #[logic]
            fn cmp_le_log(_: Self, _: Self) {
                ()
            }

            #[logic]
            fn cmp_lt_log(_: Self, _: Self) {
                ()
            }

            #[logic]
            fn cmp_ge_log(_: Self, _: Self) {
                ()
            }

            #[logic]
            fn cmp_gt_log(_: Self, _: Self) {
                ()
            }

            #[logic]
            fn refl(_: Self) {
                ()
            }

            #[logic]
            fn trans(_: Self, _: Self, _: Self, _: Ordering) {
                ()
            }

            #[logic]
            fn antisym1(_: Self, _: Self) {
                ()
            }

            #[logic]
            fn antisym2(_: Self, _: Self) {
                ()
            }

            #[logic]
            fn eq_cmp(_: Self, _: Self) {
                ()
            }
        }
    };
}

ord_logic_impl!(Int);
ord_logic_impl!(usize);
ord_logic_impl!(u64);
ord_logic_impl!(u32);
ord_logic_impl!(isize);
ord_logic_impl!(i32);
ord_logic_impl!(i64);

impl<A: OrdLogic, B: OrdLogic> OrdLogic for (A, B) {
    #[logic]
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

    #[predicate]
    fn le_log(self, o: Self) -> bool {
        pearlite! { (self.0 == o.0 && self.1 <= o.1) || self.0 <= o.0 }
    }

    #[logic]
    fn cmp_le_log(_: Self, _: Self) {}

    #[predicate]
    fn lt_log(self, o: Self) -> bool {
        pearlite! { (self.0 == o.0 && self.1 < o.1) || self.0 < o.0 }
    }

    #[logic]
    fn cmp_lt_log(_: Self, _: Self) {}

    #[predicate]
    fn ge_log(self, o: Self) -> bool {
        pearlite! { (self.0 == o.0 && self.1 >= o.1) || self.0 >= o.0 }
    }

    #[logic]
    fn cmp_ge_log(_: Self, _: Self) {}

    #[predicate]
    fn gt_log(self, o: Self) -> bool {
        pearlite! { (self.0 == o.0 && self.1 > o.1) || self.0 > o.0 }
    }

    #[logic]
    fn cmp_gt_log(_: Self, _: Self) {}

    #[logic]
    fn refl(_: Self) {}

    #[logic]
    fn trans(_: Self, _: Self, _: Self, _: Ordering) {}

    #[logic]
    fn antisym1(_: Self, _: Self) {}

    #[logic]
    fn antisym2(_: Self, _: Self) {}

    #[logic]
    fn eq_cmp(_: Self, _: Self) {}
}
