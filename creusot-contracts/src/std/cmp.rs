use crate::{logic::OrdLogic, prelude::*};
use core::cmp::*;

#[cfg(creusot)]
pub use creusot_contracts_proc::PartialEq;

#[cfg(not(creusot))]
pub use core::cmp::PartialEq;

extern_spec! {
    mod core {
        mod cmp {
            trait PartialEq<Rhs> {
                #[ensures(result == (self.deep_model() == rhs.deep_model()))]
                fn eq(&self, rhs: &Rhs) -> bool
                where
                    Self: DeepModel,
                    Rhs: DeepModel<DeepModelTy = Self::DeepModelTy>;

                #[ensures(result == (self.deep_model() != rhs.deep_model()))]
                fn ne(&self, rhs: &Rhs) -> bool
                where
                    Self: DeepModel,
                    Rhs: DeepModel<DeepModelTy = Self::DeepModelTy> {
                    !(self == rhs)
                }
            }

            // TODO: for now, we only support total orders
            trait PartialOrd<Rhs>
                where Self: DeepModel,
                      Rhs: DeepModel<DeepModelTy = Self::DeepModelTy>,
                      Self::DeepModelTy: OrdLogic
            {
                #[ensures(result == Some((*self).deep_model().cmp_log((*rhs).deep_model())))]
                fn partial_cmp(&self, rhs: &Rhs) -> Option<Ordering>;

                #[ensures(result == (self.deep_model() < other.deep_model()))]
                fn lt(&self, other: &Rhs) -> bool {
                    match self.partial_cmp(other) {
                        Some(Ordering::Less) => true,
                        _ => false,
                    }
                }

                #[ensures(result == (self.deep_model() <= other.deep_model()))]
                fn le(&self, other: &Rhs) -> bool {
                    match self.partial_cmp(other) {
                        Some(Ordering::Less | Ordering::Equal) => true,
                        _ => false,
                    }
                }

                #[ensures(result == (self.deep_model() > other.deep_model()))]
                fn gt(&self, other: &Rhs) -> bool {
                    match self.partial_cmp(other) {
                        Some(Ordering::Greater) => true,
                        _ => false,
                    }
                }

                #[ensures(result == (self.deep_model() >= other.deep_model()))]
                fn ge(&self, other: &Rhs) -> bool {
                    match self.partial_cmp(other) {
                        Some(Ordering::Greater | Ordering::Equal) => true,
                        _ => false,
                    }
                }
            }

            trait Ord
                where Self: DeepModel,
                      Self::DeepModelTy: OrdLogic
            {
                #[ensures(result == (*self).deep_model().cmp_log((*rhs).deep_model()))]
                fn cmp(&self, rhs: &Self) -> Ordering;

                #[ensures(result.deep_model() >= self.deep_model())]
                #[ensures(result.deep_model() >= o.deep_model())]
                #[ensures(result == self || result == o)]
                #[ensures(self.deep_model() <= o.deep_model() ==> result == o)]
                #[ensures(o.deep_model() < self.deep_model() ==> result == self)]
                fn max(self, o: Self) -> Self where Self: Sized {
                    if self <= o { o } else { self }
                }

                #[ensures(result.deep_model() <= self.deep_model())]
                #[ensures(result.deep_model() <= o.deep_model())]
                #[ensures(result == self || result == o)]
                #[ensures(self.deep_model() < o.deep_model() ==> result == self)]
                #[ensures(o.deep_model() <= self.deep_model() ==> result == o)]
                fn min(self, o: Self) -> Self where Self: Sized {
                    if self < o { self } else { o }
                }

                #[requires(min.deep_model() <= max.deep_model())]
                #[ensures(result.deep_model() >= min.deep_model())]
                #[ensures(result.deep_model() <= max.deep_model())]
                #[ensures(result == self || result == min || result == max)]
                #[ensures(if self.deep_model() > max.deep_model() {
                    result == max
                } else if self.deep_model() < min.deep_model() {
                    result == min
                } else { result == self })]
                fn clamp(self, min: Self, max: Self) -> Self where Self: Sized {
                    if self > max { max } else if self < min { min } else { self }
                }
            }

            #[ensures(result.deep_model() >= v1.deep_model())]
            #[ensures(result.deep_model() >= v2.deep_model())]
            #[ensures(result == v1 || result == v2)]
            #[ensures(v1.deep_model() <= v2.deep_model() ==> result == v2)]
            #[ensures(v2.deep_model() < v1.deep_model() ==> result == v1)]
            fn max<T>(v1: T, v2: T) -> T
                where T: Ord + DeepModel, T::DeepModelTy: OrdLogic
            {
                <T as Ord>::max(v1, v2)
            }

            #[ensures(result.deep_model() <= v1.deep_model())]
            #[ensures(result.deep_model() <= v2.deep_model())]
            #[ensures(result == v1 || result == v2)]
            #[ensures(v1.deep_model() < v2.deep_model() ==> result == v1)]
            #[ensures(v2.deep_model() <= v1.deep_model() ==> result == v2)]
            fn min<T>(v1: T, v2: T) -> T
                where T: Ord + DeepModel, T::DeepModelTy: OrdLogic
            {
                <T as Ord>::min(v1, v2)
            }
        }
    }
}

// Make equality and comparisons on integers pure operations.
macro_rules! impl_cmp_int {
    ($($t:ty)*) => {
$(

extern_spec! {
    impl PartialEq<$t> for $t {
        #[check(ghost)]
        #[ensures(result == (self.deep_model() == rhs.deep_model()))]
        fn eq(&self, rhs: &$t) -> bool;

        #[check(ghost)]
        #[ensures(result == (self.deep_model() != rhs.deep_model()))]
        fn ne(&self, rhs: &$t) -> bool;
    }

    impl PartialOrd<$t> for $t
    {
        #[check(ghost)]
        #[ensures(result == Some((*self).deep_model().cmp_log((*rhs).deep_model())))]
        fn partial_cmp(&self, rhs: &$t) -> Option<Ordering>;

        #[check(ghost)]
        #[ensures(result == (self.deep_model() < other.deep_model()))]
        fn lt(&self, other: &$t) -> bool {
            match self.partial_cmp(other) {
                Some(Ordering::Less) => true,
                _ => false,
            }
        }

        #[check(ghost)]
        #[ensures(result == (self.deep_model() <= other.deep_model()))]
        fn le(&self, other: &$t) -> bool {
            match self.partial_cmp(other) {
                Some(Ordering::Less | Ordering::Equal) => true,
                _ => false,
            }
        }

        #[check(ghost)]
        #[ensures(result == (self.deep_model() > other.deep_model()))]
        fn gt(&self, other: &$t) -> bool {
            match self.partial_cmp(other) {
                Some(Ordering::Greater) => true,
                _ => false,
            }
        }

        #[check(ghost)]
        #[ensures(result == (self.deep_model() >= other.deep_model()))]
        fn ge(&self, other: &$t) -> bool {
            match self.partial_cmp(other) {
                Some(Ordering::Greater | Ordering::Equal) => true,
                _ => false,
            }
        }
    }

    impl Ord for $t
    {
        #[check(ghost)]
        #[ensures(result == (*self).deep_model().cmp_log((*rhs).deep_model()))]
        fn cmp(&self, rhs: &Self) -> Ordering;

        // TODO: cannot write a `#[check(ghost)]` extern specs for the rest of the
        // items, because they have a default implementation, which means we
        // cannot differentiate an extern spec for `Ord::max` from a one for
        // `<$t as Ord>::max`.

        // #[check(ghost)]
        // #[ensures(result.deep_model() >= self.deep_model())]
        // #[ensures(result.deep_model() >= o.deep_model())]
        // #[ensures(result == self || result == o)]
        // #[ensures(self.deep_model() <= o.deep_model() ==> result == o)]
        // #[ensures(o.deep_model() < self.deep_model() ==> result == self)]
        // fn max(self, o: Self) -> Self;

        // #[check(ghost)]
        // #[ensures(result.deep_model() <= self.deep_model())]
        // #[ensures(result.deep_model() <= o.deep_model())]
        // #[ensures(result == self || result == o)]
        // #[ensures(self.deep_model() < o.deep_model() ==> result == self)]
        // #[ensures(o.deep_model() <= self.deep_model() ==> result == o)]
        // fn min(self, o: Self) -> Self;

        // #[check(ghost)]
        // #[requires(min.deep_model() <= max.deep_model())]
        // #[ensures(result.deep_model() >= min.deep_model())]
        // #[ensures(result.deep_model() <= max.deep_model())]
        // #[ensures(result == self || result == min || result == max)]
        // #[ensures(if self.deep_model() > max.deep_model() {
        //     result == max
        // } else if self.deep_model() < min.deep_model() {
        //     result == min
        // } else { result == self })]
        // fn clamp(self, min: Self, max: Self) -> Self;
    }
}

)* };

}

impl_cmp_int!(i8 i16 i32 i64 i128 isize u8 u16 u32 u64 u128 usize);

impl<T: DeepModel> DeepModel for Reverse<T> {
    type DeepModelTy = Reverse<T::DeepModelTy>;

    #[logic(open, inline)]
    fn deep_model(self) -> Self::DeepModelTy {
        pearlite! { Reverse(self.0.deep_model()) }
    }
}

impl<T: OrdLogic> OrdLogic for Reverse<T> {
    #[logic(open)]
    fn cmp_log(self, o: Self) -> Ordering {
        match self.0.cmp_log(o.0) {
            Ordering::Equal => Ordering::Equal,
            Ordering::Less => Ordering::Greater,
            Ordering::Greater => Ordering::Less,
        }
    }

    #[logic(open, law)]
    #[ensures(x.le_log(y) == (x.cmp_log(y) != Ordering::Greater))]
    fn cmp_le_log(x: Self, y: Self) {}

    #[logic(open, law)]
    #[ensures(x.lt_log(y) == (x.cmp_log(y) == Ordering::Less))]
    fn cmp_lt_log(x: Self, y: Self) {}

    #[logic(open, law)]
    #[ensures(x.ge_log(y) == (x.cmp_log(y) != Ordering::Less))]
    fn cmp_ge_log(x: Self, y: Self) {}

    #[logic(open, law)]
    #[ensures(x.gt_log(y) == (x.cmp_log(y) == Ordering::Greater))]
    fn cmp_gt_log(x: Self, y: Self) {}

    #[logic(open, law)]
    #[ensures(x.cmp_log(x) == Ordering::Equal)]
    fn refl(x: Self) {}

    #[logic(open, law)]
    #[requires(x.cmp_log(y) == o)]
    #[requires(y.cmp_log(z) == o)]
    #[ensures(x.cmp_log(z) == o)]
    fn trans(x: Self, y: Self, z: Self, o: Ordering) {}

    #[logic(open, law)]
    #[requires(x.cmp_log(y) == Ordering::Less)]
    #[ensures(y.cmp_log(x) == Ordering::Greater)]
    fn antisym1(x: Self, y: Self) {}

    #[logic(open, law)]
    #[requires(x.cmp_log(y) == Ordering::Greater)]
    #[ensures(y.cmp_log(x) == Ordering::Less)]
    fn antisym2(x: Self, y: Self) {}

    #[logic(open, law)]
    #[ensures((x == y) == (x.cmp_log(y) == Ordering::Equal))]
    fn eq_cmp(x: Self, y: Self) {}
}
