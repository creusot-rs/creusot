use crate::*;

/// A (possibly infinite) set type.
#[trusted]
#[cfg_attr(creusot, creusot::builtins = "set.Set.set")]
pub struct Set<T: ?Sized>(std::marker::PhantomData<T>);

impl<T: ?Sized> Set<T> {
    /// The empty set.
    #[cfg(creusot)]
    #[trusted]
    #[creusot::builtins = "set.Set.empty"]
    pub const EMPTY: Self = { Set(std::marker::PhantomData) };

    /// Returns `true` if `e` is in the set.
    #[open]
    #[predicate]
    #[creusot::why3_attr = "inline:trivial"]
    pub fn contains(self, e: T) -> bool {
        Self::mem(e, self)
    }

    /// [`Self::contains`], but with the order of arguments flipped.
    ///
    /// This is how the function is defined in why3.
    #[doc(hidden)]
    #[trusted]
    #[predicate]
    #[creusot::builtins = "set.Set.mem"]
    pub fn mem(_: T, _: Self) -> bool {
        dead
    }

    /// Returns a new set, where `e` has been added if it was not present.
    #[open]
    #[logic]
    #[creusot::why3_attr = "inline:trivial"]
    pub fn insert(self, e: T) -> Self {
        Self::add(e, self)
    }

    /// [`Self::insert`], but with the order of arguments flipped.
    ///
    /// This is how the function is defined in why3.
    #[doc(hidden)]
    #[trusted]
    #[logic]
    #[creusot::builtins = "set.Set.add"]
    pub fn add(_: T, _: Self) -> Self {
        dead
    }

    /// Returns `true` if the set contains no elements.
    #[trusted]
    #[predicate]
    #[creusot::builtins = "set.Set.is_empty"]
    pub fn is_empty(self) -> bool {
        dead
    }

    /// Returns a new set, where `e` is no longer present.
    #[open]
    #[logic]
    #[creusot::why3_attr = "inline:trivial"]
    pub fn remove(self, a: T) -> Self {
        Self::rem(a, self)
    }

    /// [`Self::remove`], but with the order of arguments flipped.
    ///
    /// This is how the function is defined in why3.
    #[doc(hidden)]
    #[trusted]
    #[logic]
    #[creusot::builtins = "set.Set.remove"]
    pub fn rem(_: T, _: Self) -> Self {
        dead
    }

    /// Returns a new set, which is the union of `self` and `other`.
    ///
    /// An element is in the result if it is in `self` _or_ if it is in `other`.
    #[trusted]
    #[logic]
    #[creusot::builtins = "set.Set.union"]
    pub fn union(self, _: Self) -> Self {
        dead
    }
}
