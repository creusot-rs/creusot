//! Some useful logical items

use crate::*;

/// A wrapper around `T` that makes it safe.
///
/// This type is indented to be used in logic code.
pub type SizedW<T> = Box<T>;

/// Helper trait to turn a `T` into a [`SizedW<T>`]
pub trait MakeSized {
    /// Turn a `T` into a [`SizedW<T>`]
    #[logic]
    #[creusot::why3_attr = "inline:trivial"]
    fn make_sized(&self) -> SizedW<Self>;
}

impl<T: ?Sized> MakeSized for T {
    #[trusted]
    #[logic]
    #[ensures(*result == *self)]
    fn make_sized(&self) -> SizedW<Self> {
        dead
    }
}

/// Creates a logical value satisfying the property given by `p`.
///
/// This is also called the "epsilon operator": its goal is not extract from `∃x. P(x)`
/// a `x` satisfying `P`.
#[trusted]
#[logic]
#[requires(exists<x: T> p[x])]
#[ensures(p[result])]
pub fn such_that<T>(p: crate::logic::Mapping<T, bool>) -> T {
    dead
}

/// Indicates unreachable code.
///
/// This function indicates a logical branch that should be impossible to reach.
#[trusted]
#[allow(unconditional_recursion)]
#[logic]
#[requires(false)]
#[ensures(false)]
#[variant(0)]
pub fn unreachable<T>() -> T {
    unreachable()
}
