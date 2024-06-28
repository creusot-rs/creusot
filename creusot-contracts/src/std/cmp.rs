use crate::{logic::OrdLogic, *};
pub use ::std::cmp::*;

#[cfg(creusot)]
pub use creusot_contracts_proc::PartialEq;

extern_spec! {
    mod std {
        mod cmp {
            trait PartialEq<Rhs> {
                #[ensures(result == (self.eq_model() == rhs.eq_model()))]
                fn eq(&self, rhs: &Rhs) -> bool
                where
                    Self: EqModel,
                    Rhs: EqModel<EqModelTy = Self::EqModelTy>;

                #[ensures(result == (self.eq_model() != rhs.eq_model()))]
                fn ne(&self, rhs: &Rhs) -> bool
                where
                    Self: EqModel,
                    Rhs: EqModel<EqModelTy = Self::EqModelTy>;
            }

            // TODO: for now, we only support total orders
            trait PartialOrd<Rhs>
                where Self: EqModel,
                      Rhs: EqModel<EqModelTy = Self::EqModelTy>,
                      Self::EqModelTy: OrdLogic
            {
                #[ensures(result == Some((*self).eq_model().cmp_log((*rhs).eq_model())))]
                fn partial_cmp(&self, rhs: &Rhs) -> Option<Ordering>;

                #[ensures(result == (self.eq_model() < other.eq_model()))]
                fn lt(&self, other: &Rhs) -> bool;

                #[ensures(result == (self.eq_model() <= other.eq_model()))]
                fn le(&self, other: &Rhs) -> bool;

                #[ensures(result == (self.eq_model() > other.eq_model()))]
                fn gt(&self, other: &Rhs) -> bool;

                #[ensures(result == (self.eq_model() >= other.eq_model()))]
                fn ge(&self, other: &Rhs) -> bool;
            }

            trait Ord
                where Self: EqModel,
                      Self::EqModelTy: OrdLogic
            {
                #[ensures(result == (*self).eq_model().cmp_log((*rhs).eq_model()))]
                fn cmp(&self, rhs: &Self) -> Ordering;

                #[ensures(result.eq_model() >= self.eq_model())]
                #[ensures(result.eq_model() >= o.eq_model())]
                #[ensures(result == self || result == o)]
                #[ensures(self.eq_model() <= o.eq_model() ==> result == o)]
                #[ensures(o.eq_model() < self.eq_model() ==> result == self)]
                fn max(self, o: Self) -> Self;
            }
        }
    }
}

impl<T: EqModel> EqModel for Reverse<T> {
    type EqModelTy = Reverse<T::EqModelTy>;

    #[logic]
    #[open]
    fn eq_model(self) -> Self::EqModelTy {
        pearlite! { Reverse(self.0.eq_model()) }
    }
}

impl<T: OrdLogic> OrdLogic for Reverse<T> {
    #[logic]
    #[open]
    fn cmp_log(self, o: Self) -> Ordering {
        match self.0.cmp_log(o.0) {
            Ordering::Equal => Ordering::Equal,
            Ordering::Less => Ordering::Greater,
            Ordering::Greater => Ordering::Less,
        }
    }

    #[law]
    #[open]
    #[ensures(x.le_log(y) == (x.cmp_log(y) != Ordering::Greater))]
    fn cmp_le_log(x: Self, y: Self) {}

    #[law]
    #[open]
    #[ensures(x.lt_log(y) == (x.cmp_log(y) == Ordering::Less))]
    fn cmp_lt_log(x: Self, y: Self) {}

    #[law]
    #[open]
    #[ensures(x.ge_log(y) == (x.cmp_log(y) != Ordering::Less))]
    fn cmp_ge_log(x: Self, y: Self) {}

    #[law]
    #[open]
    #[ensures(x.gt_log(y) == (x.cmp_log(y) == Ordering::Greater))]
    fn cmp_gt_log(x: Self, y: Self) {}

    #[law]
    #[open]
    #[ensures(x.cmp_log(x) == Ordering::Equal)]
    fn refl(x: Self) {}

    #[law]
    #[open]
    #[requires(x.cmp_log(y) == o)]
    #[requires(y.cmp_log(z) == o)]
    #[ensures(x.cmp_log(z) == o)]
    fn trans(x: Self, y: Self, z: Self, o: Ordering) {}

    #[law]
    #[open]
    #[requires(x.cmp_log(y) == Ordering::Less)]
    #[ensures(y.cmp_log(x) == Ordering::Greater)]
    fn antisym1(x: Self, y: Self) {}

    #[law]
    #[open]
    #[requires(x.cmp_log(y) == Ordering::Greater)]
    #[ensures(y.cmp_log(x) == Ordering::Less)]
    fn antisym2(x: Self, y: Self) {}

    #[law]
    #[open]
    #[ensures((x == y) == (x.cmp_log(y) == Ordering::Equal))]
    fn eq_cmp(x: Self, y: Self) {}
}
