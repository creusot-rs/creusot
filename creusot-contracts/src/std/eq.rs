use crate as creusot_contracts;
use creusot_contracts_proc::*;

use crate::logic::*;

extern_spec! {
    mod std {
        mod cmp {
            trait PartialEq<Rhs> {
                #[ensures(result == (@self == @rhs))]
                fn eq(&self, rhs: &Rhs) -> bool
                where
                    Self: Model,
                    Rhs: Model<ModelTy = Self::ModelTy>;

            }
        }
    }
}
