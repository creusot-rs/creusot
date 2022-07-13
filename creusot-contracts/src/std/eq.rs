use crate as creusot_contracts;
use creusot_contracts_proc::*;
use std::alloc::Allocator;

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
        mod boxed {
            impl<T, A : Allocator> PartialEq<Box<T, A>> for Box<T, A> {
                #[ensures(result == (@self == @rhs))]
                fn eq(&self, rhs: &Self) -> bool
                where
                    T : Model,
                    T: PartialEq<T> + ?Sized,
                    A: Allocator;
            }
        }
    }
}
