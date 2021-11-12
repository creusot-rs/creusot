use crate as creusot_contracts;
use crate::logic::Int;
use creusot_contracts_proc::*;

#[allow(unused)]
pub trait EqLogic {
    #[predicate]
    fn log_eq(self, _: Self) -> bool;

    #[predicate]
    fn log_ne(self, _: Self) -> bool;

    #[logic]
    #[ensures(!(a.log_eq(b) === a.log_ne(b)))]
    fn eq_ne(a: Self, b: Self);

    #[logic]
    #[ensures(x == x)]
    fn refl(x: Self);

    #[logic]
    #[requires(x == y)]
    #[ensures(y == x)]
    fn symmetry(x: Self, y: Self);

    #[logic]
    #[requires(x == y)]
    #[requires(y == z)]
    #[ensures(x == z)]
    fn transitivity(x: Self, y: Self, z: Self);
}

macro_rules! eq_logic_impl {
    ($t:ty) => {
        impl EqLogic for $t {
            #[predicate]
            #[creusot::builtins = "=="]
            fn log_eq(self, _: Self) -> bool {
                true
            }

            #[predicate]
            #[creusot::builtins = "!="]
            fn log_ne(self, _: Self) -> bool {
                false
            }

            #[logic]
            fn eq_ne(_: Self, _: Self) {}

            #[logic]
            fn refl(_: Self) {}

            #[logic]
            fn symmetry(_: Self, _: Self) {}

            #[logic]
            fn transitivity(_: Self, _: Self, _: Self) {}
        }
    };
}

eq_logic_impl!(Int);
eq_logic_impl!(usize);
eq_logic_impl!(u64);
eq_logic_impl!(u32);
eq_logic_impl!(isize);
eq_logic_impl!(i64);
eq_logic_impl!(i32);
eq_logic_impl!(bool);
