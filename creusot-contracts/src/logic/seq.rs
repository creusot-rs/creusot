use crate as creusot_contracts;
use creusot_contracts_proc::*;

use crate::logic::*;
use crate::Int;
use std::ops::Index;

#[creusot::builtins = "seq.Seq.seq"]
pub struct Seq<T: ?Sized>(std::marker::PhantomData<T>);

impl<T> EqLogic for Seq<T> {
    #[predicate]
    #[creusot::builtins = "seq.Seq.(==)"]
    fn log_eq(self, _: Self) -> bool {
        true
    }

    #[predicate]
    fn log_ne(self, o: Self) -> bool {
        pearlite! { !(self == o)}
    }

    #[logic]
    fn eq_ne(_: Self, _: Self) {
        ()
    }

    #[logic]
    fn refl(_: Self) {
        ()
    }

    #[logic]
    fn symmetry(_: Self, _: Self) {
        ()
    }

    #[logic]
    fn transitivity(_: Self, _: Self, _: Self) {
        ()
    }
}

impl<T> Seq<T> {
    #[trusted]
    #[creusot::builtins = "seq.Seq.empty"]
    pub const EMPTY: Self = { panic!() };

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
    #[logic]
    #[creusot::builtins = "seq.Seq.snoc"]
    pub fn push(self, _: T) -> Self {
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
}

// A hack which allows us to use [..] notation for sequences.
// Relies on the fact we don't enforce that implementations of traits are of
// the same function type as the trait signature.. When this is addressed
// the following instance will error.
impl<T> std::ops::Index<Int> for Seq<T> {
    type Output = T;

    #[trusted]
    #[logic]
    #[creusot::builtins = "seq.Seq.get"]
    fn index(&self, _: Int) -> &T {
        absurd
    }
}
