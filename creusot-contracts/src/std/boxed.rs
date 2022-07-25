use crate as creusot_contracts;
use creusot_contracts_proc::*;

use std::alloc::Allocator;

extern_spec! {
    mod std {
        mod boxed {
            impl<T> Box<T> {
                #[ensures(*result == val)]
                fn new(val: T) -> Self;
            }

            impl<T, A: Allocator> Box<T, A> {
                #[ensures(**self == *result)]
                #[ensures(*^self == ^result)]
                fn as_mut(&mut self) -> &mut T;

                #[ensures(**self == *result)]
                fn as_ref(&self) -> &T;
            }
        }
    }
}
