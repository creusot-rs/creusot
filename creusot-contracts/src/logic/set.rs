use crate::{logic::Mapping, prelude::*};
use std::marker::PhantomData;

/// A (possibly infinite) set type.
#[opaque]
#[builtin("set.Set.set")]
pub struct Set<T: ?Sized>(PhantomData<T>);

impl<T: ?Sized> Set<T> {
    /// The empty set.
    #[logic]
    #[builtin("set.Set.empty", ascription)]
    pub fn empty() -> Self {
        dead
    }

    /// Build a set from a predicate, given as a `Mapping`.
    #[logic]
    #[builtin("identity")]
    pub fn from_predicate(_: Mapping<T, bool>) -> Self {
        dead
    }

    /// Returns `true` if `e` is in the set.
    #[logic(open, inline)]
    pub fn contains(self, e: T) -> bool {
        Self::mem(e, self)
    }

    /// [`Self::contains`], but with the order of arguments flipped.
    ///
    /// This is how the function is defined in why3.
    #[doc(hidden)]
    #[logic]
    #[builtin("set.Set.mem")]
    pub fn mem(_: T, _: Self) -> bool {
        dead
    }

    /// Returns a new set, where `e` has been added if it was not present.
    #[logic(open, inline)]
    pub fn insert(self, e: T) -> Self {
        Self::add(e, self)
    }

    /// [`Self::insert`], but with the order of arguments flipped.
    ///
    /// This is how the function is defined in why3.
    #[doc(hidden)]
    #[logic]
    #[builtin("set.Set.add")]
    pub fn add(_: T, _: Self) -> Self {
        dead
    }

    /// Returns `true` if the set contains no elements.
    #[logic]
    #[builtin("set.Set.is_empty")]
    pub fn is_empty(self) -> bool {
        dead
    }

    /// Returns a new set, where `e` is no longer present.
    #[logic(open, inline)]
    pub fn remove(self, a: T) -> Self {
        Self::rem(a, self)
    }

    /// [`Self::remove`], but with the order of arguments flipped.
    ///
    /// This is how the function is defined in why3.
    #[doc(hidden)]
    #[logic]
    #[builtin("set.Set.remove")]
    pub fn rem(_: T, _: Self) -> Self {
        dead
    }

    /// Returns a new set, which is the union of `self` and `other`.
    ///
    /// An element is in the result if it is in `self` _or_ if it is in `other`.
    #[logic]
    #[builtin("set.Set.union")]
    pub fn union(self, _: Self) -> Self {
        dead
    }
}
