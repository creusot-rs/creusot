use crate::{logic::{PartialOrdLogic, OrdLogic}, *};
pub use ::std::cmp::*;

#[cfg(creusot)]
pub use creusot_contracts_proc::PartialEq;

extern_spec! {
    mod std {
        mod cmp {
            trait PartialEq<Rhs> {
                #[ensures(result == (self.deep_model() == rhs.deep_model()))]
                fn eq(&self, rhs: &Rhs) -> bool
                where
                    Self: DeepModel,
                    Rhs: DeepModel<DeepModelTy = Self::DeepModelTy>;
            }

            trait PartialOrd<Rhs>
                where Self: DeepModel,
                      Rhs: ?Sized + DeepModel<DeepModelTy = Self::DeepModelTy>,
                      Self::DeepModelTy: PartialOrdLogic
            {
                #[ensures(result == self.deep_model().partial_cmp_log(other.deep_model()))]
                fn partial_cmp(&self, other: &Rhs) -> Option<Ordering>;

                #[ensures(result == (self.deep_model() < other.deep_model()))]
                fn lt(&self, other: &Rhs) -> bool;

                #[ensures(result == (self.deep_model() <= other.deep_model()))]
                fn le(&self, other: &Rhs) -> bool;

                #[ensures(result == (self.deep_model() > other.deep_model()))]
                fn gt(&self, other: &Rhs) -> bool;

                #[ensures(result == (self.deep_model() >= other.deep_model()))]
                fn ge(&self, other: &Rhs) -> bool;
            }

            trait Ord
                where Self: DeepModel + PartialOrd<Self>,
                      Self::DeepModelTy: OrdLogic
            {
                #[ensures(result == self.deep_model().cmp_log(rhs.deep_model()))]
                fn cmp(&self, rhs: &Self) -> Ordering;

                #[ensures(result.deep_model() >= self.deep_model())]
                #[ensures(result.deep_model() >= o.deep_model())]
                #[ensures(result == self || result == o)]
                #[ensures(self.deep_model() <= o.deep_model() ==> result == o)]
                #[ensures(o.deep_model() < self.deep_model() ==> result == self)]
                fn max(self, o: Self) -> Self;
            }
        }
    }
}

impl<T: DeepModel> DeepModel for Reverse<T> {
    type DeepModelTy = Reverse<T::DeepModelTy>;

    #[logic]
    fn deep_model(self) -> Self::DeepModelTy {
        pearlite! { Reverse(self.0.deep_model()) }
    }
}

impl<T: PartialOrdLogic> PartialOrdLogic for Reverse<T> {
    #[predicate]
    fn lt_log(self, other: Self) -> bool {
        self.0.gt_log(other.0)
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

impl<T: OrdLogic> OrdLogic for Reverse<T> {
    #[law]
    #[ensures(x.lt_log(y) || x == y || y.lt_log(x))]
    fn trichotomy(x: Self, y: Self) {
        T::trichotomy(y.0, x.0)
    }
}
