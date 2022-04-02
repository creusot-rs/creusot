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
                    Self_: Model,
                    Rhs: Model<ModelTy = Self_::ModelTy>;

            }
        }
    }
}


impl<T : Eq> Eq for Option<T> {
    #[trusted]
    #[ensures(result === (*self == *rhs))]
    fn eq(&self, rhs: &Self) -> bool {
        match (self, rhs) {
            (Some(x), Some(y)) => x.eq(y),
            (None, None) => true,
            _ => false
        }
    }   
}