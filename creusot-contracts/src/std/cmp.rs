use crate as creusot_contracts;
use creusot_contracts_proc::*;

use crate::{logic::ord::*, DeepModel};
use std::cmp::Ordering;

extern_spec! {
    mod std {
        mod cmp {
            // TODO: for now, we only support total orders
            trait PartialOrd<Rhs>
                where Self: DeepModel,
                      Rhs: DeepModel<DeepModelTy = Self::DeepModelTy>,
                      Self::DeepModelTy: OrdLogic
            {
                #[ensures(result == Some((*self).deep_model().cmp_log((*rhs).deep_model())))]
                fn partial_cmp(&self, rhs: &Rhs) -> Option<Ordering>;

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
                fn max(self, o: Self) -> Self;
            }
        }
    }
}
