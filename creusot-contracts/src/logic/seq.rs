use crate as creusot_contracts;
use crate::macros::*;

use crate::{logic::*, Int};
use std::ops::Index;

impl<T: ?Sized> Copy for Seq<T> {}
impl<T: ?Sized> Clone for Seq<T> {
    fn clone(&self) -> Self {
        *self
    }
}
#[cfg_attr(feature = "contracts", creusot::builtins = "seq.Seq.seq")]
pub struct Seq<T: ?Sized>(std::marker::PhantomData<T>);

impl<T> Seq<T> {
    #[cfg(feature = "contracts")]
    #[trusted]
    #[creusot::builtins = "seq.Seq.empty"]
    pub const EMPTY: Self = { Seq(std::marker::PhantomData) };

    #[logic]
    pub fn new() -> Self {
        Self::EMPTY
    }

    #[logic]
    pub fn get(self, ix: Int) -> Option<T> {
        if ix < self.len() {
            Some(*self.index(ix))
        } else {
            None
        }
    }

    #[trusted]
    #[logic]
    #[creusot::builtins = "seq_ext.SeqExt.subsequence"]
    pub fn subsequence(self, _: Int, _: Int) -> Self {
        absurd
    }

    #[trusted]
    #[logic]
    #[creusot::builtins = "seq.Seq.singleton"]
    pub fn singleton(_: T) -> Self {
        absurd
    }

    #[logic]
    pub fn tail(self) -> Self {
        self.subsequence(1, self.len())
    }

    #[trusted]
    #[logic]
    #[creusot::builtins = "seq.Seq.length"]
    pub fn len(self) -> Int {
        absurd
    }

    #[trusted]
    #[logic]
    #[creusot::builtins = "seq.Seq.set"]
    pub fn set(self, _: Int, _: T) -> Self {
        absurd
    }

    #[trusted]
    #[predicate]
    #[creusot::builtins = "seq.Seq.(==)"]
    pub fn ext_eq(self, _: Self) -> bool {
        absurd
    }

    #[trusted]
    #[logic]
    #[creusot::builtins = "seq.Seq.snoc"]
    pub fn push(self, _: T) -> Self {
        absurd
    }

    #[trusted]
    #[logic]
    #[creusot::builtins = "seq.Seq.(++)"]
    pub fn concat(self, _: Self) -> Self {
        absurd
    }

    #[predicate]
    pub fn permutation_of(self, o: Self) -> bool {
        self.permut(o, 0, self.len())
    }

    #[trusted]
    #[predicate]
    #[creusot::builtins = "seq.Permut.permut"]
    pub fn permut(self, _: Self, _: Int, _: Int) -> bool {
        absurd
    }

    #[trusted]
    #[predicate]
    #[creusot::builtins = "seq.Permut.exchange"]
    pub fn exchange(self, _: Self, _: Int, _: Int) -> bool {
        absurd
    }

    #[predicate]
    pub fn contains(self, e: T) -> bool {
        pearlite! { exists<i : Int> 0 <= i &&  i <self.len() && self[i] == e }
    }

    // A hack to trigger loading the `seq.FreeMonoid` module which is quite useful
    #[logic]
    #[creusot::builtins = "seq.FreeMonoid.left_neutral"]
    pub fn left_neutral(self) {}
}

// A hack which allows us to use [..] notation for sequences.
// Relies on the fact we don't enforce that implementations of traits are of
// the same function type as the trait signature.. When this is addressed
// the following instance will error.
#[cfg(feature = "contracts")]
impl<T> std::ops::Index<Int> for Seq<T> {
    type Output = T;

    #[trusted]
    #[logic]
    #[creusot::builtins = "seq.Seq.get"]
    fn index(&self, _: Int) -> &T {
        absurd
    }
}
