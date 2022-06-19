use crate as creusot_contracts;
use creusot_contracts_proc::*;

use crate::logic::*;
use crate::Int;
use std::ops::Index;

#[creusot::builtins = "set.Set.set"]
pub struct Set<T: ?Sized>(std::marker::PhantomData<T>);

impl<T: ?Sized> Set<T> {
    #[predicate]
    #[creusot::builtins = "set.Set.mem"]
    pub fn contains(self, e: T) -> bool {
        pearlite! {absurd}
    }

    #[predicate]
    #[creusot::builtins = "set.Set.add"]
    pub fn insert(self, e: T) -> Self {
        pearlite! { absurd }
    }
}
