use crate::{std::cmp::Ordering, util::*, *};

#[allow(unused)]
pub trait PartialOrdLogic {
    #[predicate]
    fn lt_log(self, _: Self) -> bool;

    #[law]
    #[ensures(!self.lt_log(self))]
    fn lt_log_irrefl(self);

    #[law]
    #[requires(x.lt_log(y))]
    #[ensures(!y.lt_log(x))]
    fn lt_log_asymm(x: Self, y: Self);

    #[law]
    #[requires(x.lt_log(y))]
    #[requires(y.lt_log(z))]
    #[ensures(x.lt_log(z))]
    fn lt_log_trans(x: Self, y: Self, z: Self);

    #[predicate]
    #[ensures(result == other.lt_log(self))]
    fn gt_log(self, other: Self) -> bool {
        other.lt_log(self)
    }

    #[predicate]
    #[ensures(result == (self.lt_log(other) || self == other))]
    fn le_log(self, other: Self) -> bool {
        self.lt_log(other) || self == other
    }

    #[law]
    #[ensures(self.le_log(self))]
    fn le_log_refl(self) {}

    #[law]
    #[requires(x.le_log(y))]
    #[requires(y.le_log(x))]
    #[ensures(x == y)]
    fn le_log_anti(x: Self, y: Self) {
        Self::lt_log_asymm(x, y)
    }

    #[law]
    #[requires(x.le_log(y))]
    #[requires(y.le_log(z))]
    #[ensures(x.le_log(z))]
    fn le_log_trans(x: Self, y: Self, z: Self) {
        Self::lt_log_trans(x, y, z);
    }

    #[predicate]
    #[ensures(result == other.le_log(self))]
    fn ge_log(self, other: Self) -> bool {
        other.le_log(self)
    }

    #[logic]
    #[ensures((result == Some(Ordering::Less)) == self.lt_log(other))]
    #[ensures((result == Some(Ordering::Equal)) == (self == other))]
    #[ensures((result == Some(Ordering::Greater)) == self.gt_log(other))]
    fn partial_cmp_log(self, other: Self) -> Option<Ordering> {
        Self::lt_log_asymm(self, other);

        if self.lt_log(other) {
            Some(Ordering::Less)
        } else if self == other {
            Some(Ordering::Equal)
        } else if other.lt_log(self) {
            Some(Ordering::Greater)
        } else {
            None
        }
    }
}

#[allow(unused)]
pub trait OrdLogic: PartialOrdLogic {
    #[logic]
    #[ensures(self.partial_cmp_log(other) == Some(result))]
    fn cmp_log(self, other: Self) -> Ordering {
        Self::trichotomy(self, other);

        unwrap(self.partial_cmp_log(other))
    }

    #[law]
    #[ensures(x.lt_log(y) || x == y || y.lt_log(x))]
    fn trichotomy(x: Self, y: Self);
}

macro_rules! ord_logic_impl {
    ($t:ty) => {
        impl PartialOrdLogic for $t {
            #[predicate]
            #[creusot::builtins = "int.Int.(<)"]
            fn lt_log(self, _: Self) -> bool {
                pearlite! { absurd }
            }

            #[predicate]
            #[creusot::builtins = "int.Int.(<=)"]
            fn le_log(self, _: Self) -> bool {
                pearlite! { absurd }
            }

            #[predicate]
            #[creusot::builtins = "int.Int.(>)"]
            fn gt_log(self, _: Self) -> bool {
                pearlite! { absurd }
            }

            #[predicate]
            #[creusot::builtins = "int.Int.(>=)"]
            fn ge_log(self, _: Self) -> bool {
                pearlite! { absurd }
            }

            #[law]
            #[ensures(!self.lt_log(self))]
            fn lt_log_irrefl(self) {}

            #[law]
            #[requires(x.lt_log(y))]
            #[ensures(!y.lt_log(x))]
            fn lt_log_asymm(x: Self, y: Self) {}

            #[law]
            #[requires(x.lt_log(y))]
            #[requires(y.lt_log(z))]
            #[ensures(x.lt_log(z))]
            fn lt_log_trans(x: Self, y: Self, z: Self) {}
        }

        impl OrdLogic for $t {
            #[law]
            #[ensures(x.lt_log(y) || x == y || y.lt_log(x))]
            fn trichotomy(x: Self, y: Self) {}
        }
    };
}

ord_logic_impl!(Int);

ord_logic_impl!(u8);
ord_logic_impl!(u16);
ord_logic_impl!(u32);
ord_logic_impl!(u64);
ord_logic_impl!(u128);
ord_logic_impl!(usize);

ord_logic_impl!(i8);
ord_logic_impl!(i16);
ord_logic_impl!(i32);
ord_logic_impl!(i64);
ord_logic_impl!(i128);
ord_logic_impl!(isize);

impl<A: PartialOrdLogic, B: PartialOrdLogic> PartialOrdLogic for (A, B) {
    #[predicate]
    fn lt_log(self, other: Self) -> bool {
        self.0.lt_log(other.0) || (self.0 == other.0 && self.1.lt_log(other.1))
    }

    #[law]
    #[ensures(!self.lt_log(self))]
    fn lt_log_irrefl(self) {}

    #[law]
    #[requires(x.lt_log(y))]
    #[ensures(!y.lt_log(x))]
    fn lt_log_asymm(x: Self, y: Self) {}

    #[law]
    #[requires(x.lt_log(y))]
    #[requires(y.lt_log(z))]
    #[ensures(x.lt_log(z))]
    fn lt_log_trans(x: Self, y: Self, z: Self) {}
}

impl<A: OrdLogic, B: OrdLogic> OrdLogic for (A, B) {
    #[law]
    #[ensures(x.lt_log(y) || x == y || y.lt_log(x))]
    fn trichotomy(x: Self, y: Self) {
        A::trichotomy(x.0, y.0);
        B::trichotomy(x.1, y.1);
    }
}

impl<T: PartialOrdLogic> PartialOrdLogic for Option<T> {
    #[predicate]
    fn lt_log(self, other: Self) -> bool {
        match (self, other) {
            (None, Some(_)) => true,
            (Some(x), Some(y)) => x.lt_log(y),
            _ => false,
        }
    }

    #[law]
    #[ensures(!self.lt_log(self))]
    fn lt_log_irrefl(self) {}

    #[law]
    #[requires(x.lt_log(y))]
    #[ensures(!y.lt_log(x))]
    fn lt_log_asymm(x: Self, y: Self) {}

    #[law]
    #[requires(x.lt_log(y))]
    #[requires(y.lt_log(z))]
    #[ensures(x.lt_log(z))]
    fn lt_log_trans(x: Self, y: Self, z: Self) {}
}

impl<T: OrdLogic> OrdLogic for Option<T> {
    #[law]
    #[ensures(x.lt_log(y) || x == y || y.lt_log(x))]
    fn trichotomy(x: Self, y: Self) {
        match (x, y) {
            (Some(x), Some(y)) => T::trichotomy(x, y),
            _ => (),
        }
    }
}

