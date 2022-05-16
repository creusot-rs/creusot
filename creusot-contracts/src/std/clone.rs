use crate as creusot_contracts;
use creusot_contracts_proc::*;

pub trait Clone: Sized {
    #[ensures(result == *self)]
    fn clone(&self) -> Self;
}

impl<T: Copy> Clone for T {
    #[trusted]
    #[ensures(result == *self)]
    fn clone(&self) -> Self {
        *self
    }
}
