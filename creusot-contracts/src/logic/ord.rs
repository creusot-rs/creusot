use crate as creusot_contracts;
use crate::logic::EqLogic;
use crate::logic::Int;
use creusot_contracts_proc::*;
pub use std::cmp::Ordering;

#[allow(unused)]
pub trait OrdLogic: EqLogic {
    #[logic]
    fn cmp_log(self, _: Self) -> Ordering;

    #[logic]
    fn le_log(self, o: Self) -> bool {
        match self.cmp_log(o) {
            Ordering::Greater => false,
            _ => true,
        }
    }

    #[logic]
    #[ensures(x.le_log(y) === ! (x.cmp_log(y) === Ordering::Greater))]
    fn cmp_le_log(x: Self, y: Self);

    #[logic]
    fn lt_log(self, o: Self) -> bool {
        match self.cmp_log(o) {
            Ordering::Less => true,
            _ => false,
        }
    }

    #[logic]
    #[ensures(x.le_log(y) === (x.cmp_log(y) === Ordering::Less))]
    fn cmp_lt_log(x: Self, y: Self);

    #[logic]
    fn ge_log(self, o: Self) -> bool {
        match self.cmp_log(o) {
            Ordering::Less => false,
            _ => true,
        }
    }

    #[logic]
    #[ensures(x.le_log(y) === ! (x.cmp_log(y) === Ordering::Less))]
    fn cmp_ge_log(x: Self, y: Self);

    #[logic]
    fn gt_log(self, o: Self) -> bool {
        match self.cmp_log(o) {
            Ordering::Greater => true,
            _ => false,
        }
    }

    #[logic]
    #[ensures(x.le_log(y) === (x.cmp_log(y) === Ordering::Greater))]
    fn cmp_gt_log(x: Self, y: Self);

    #[logic]
    #[ensures(x.cmp_log(x) === Ordering::Equal)]
    fn refl(x: Self);

    #[logic]
    #[requires(x.cmp_log(y) === o)]
    #[requires(y.cmp_log(z) === o)]
    #[ensures(x.cmp_log(z) === o)]
    fn trans(x: Self, y: Self, z: Self, o: Ordering);

    #[logic]
    #[requires(x.cmp_log(y) === Ordering::Less)]
    #[ensures(y.cmp_log(x) === Ordering::Greater)]
    fn antisym1(x: Self, y: Self);

    #[logic]
    #[requires(x.cmp_log(y) === Ordering::Greater)]
    #[ensures(y.cmp_log(x) === Ordering::Less)]
    fn antisym2(x: Self, y: Self);

    #[logic]
    #[ensures(x == y ==> x.cmp_log(y) === Ordering::Equal)]
    #[ensures(y.cmp_log(x) === Ordering::Equal ==> x == y)]
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
            #[logic]
            #[creusot::builtins = "<="]
            fn le_log(self, _: Self) -> bool {
                true
            }

            #[trusted]
            #[logic]
            #[creusot::builtins = "<"]
            fn lt_log(self, _: Self) -> bool {
                true
            }

            #[trusted]
            #[logic]
            #[creusot::builtins = ">="]
            fn ge_log(self, _: Self) -> bool {
                true
            }

            #[trusted]
            #[logic]
            #[creusot::builtins = ">"]
            fn gt_log(self, _: Self) -> bool {
                true
            }

            #[logic]
            fn cmp_le_log(_: Self, _: Self) {}

            #[logic]
            fn cmp_lt_log(_: Self, _: Self) {}

            #[logic]
            fn cmp_ge_log(_: Self, _: Self) {}

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
    };
}

ord_logic_impl!(Int);
ord_logic_impl!(usize);
ord_logic_impl!(u64);
ord_logic_impl!(u32);
ord_logic_impl!(isize);
ord_logic_impl!(i64);
ord_logic_impl!(i32);
