use crate::*;

/// A finite set type usable in pearlite and `ghost!` blocks.
///
/// If you need an infinite set, see [`Set`](super::Set).
///
/// # Ghost
///
/// Since [`std::collections::HashSet`] and [`std::collections::BTreeSet`] have finite
/// capacity, this could cause some issues in ghost code:
/// ```rust,creusot,compile_fail
/// ghost! {
///     let mut set = HashSet::new();
///     for _ in 0..=usize::MAX as u128 + 1 {
///         set.insert(0); // cannot fail, since we are in a ghost block
///     }
///     proof_assert!(set.len() <= usize::MAX@); // by definition
///     proof_assert!(set.len() > usize::MAX@); // uh-oh
/// }
/// ```
///
/// This type is designed for this use-case, with no restriction on the capacity.
#[trusted]
#[cfg_attr(creusot, creusot::builtins = "set.Fset.fset")]
pub struct FSet<T: ?Sized>(std::marker::PhantomData<T>);

impl<T: ?Sized> FSet<T> {
    /// The empty set.
    #[cfg(creusot)]
    #[trusted]
    #[creusot::builtins = "set.Fset.empty"]
    pub const EMPTY: Self = { FSet(std::marker::PhantomData) };

    /// Returns the empty set.
    #[logic]
    #[open]
    pub fn empty() -> Self {
        Self::EMPTY
    }

    /// Returns `true` if `e` is in the set.
    #[open]
    #[predicate]
    #[why3::attr = "inline:trivial"]
    pub fn contains(self, e: T) -> bool {
        Self::mem(e, self)
    }

    /// [`Self::contains`], but with the order of arguments flipped.
    ///
    /// This is how the function is defined in why3.
    #[doc(hidden)]
    #[trusted]
    #[logic]
    #[creusot::builtins = "set.Fset.mem"]
    pub fn mem(_: T, _: Self) -> bool {
        dead
    }

    /// Returns a new set, where `e` has been added if it was not present.
    #[open]
    #[logic]
    #[why3::attr = "inline:trivial"]
    pub fn insert(self, e: T) -> Self {
        Self::add(e, self)
    }

    /// [`Self::insert`], but with the order of arguments flipped.
    ///
    /// This is how the function is defined in why3.
    #[doc(hidden)]
    #[trusted]
    #[logic]
    #[creusot::builtins = "set.Fset.add"]
    pub fn add(_: T, _: Self) -> Self {
        dead
    }

    /// Returns `true` if the set contains no elements.
    #[trusted]
    #[predicate]
    #[creusot::builtins = "set.Fset.is_empty"]
    pub fn is_empty(self) -> bool {
        dead
    }

    /// Returns a new set, where `e` is not longer present.
    #[open]
    #[logic]
    #[why3::attr = "inline:trivial"]
    pub fn remove(self, e: T) -> Self {
        Self::rem(e, self)
    }

    /// [`Self::remove`], but with the order of arguments flipped.
    ///
    /// This is how the function is defined in why3.
    #[doc(hidden)]
    #[trusted]
    #[logic]
    #[creusot::builtins = "set.Fset.remove"]
    pub fn rem(_: T, _: Self) -> Self {
        dead
    }

    /// Returns a new set, which is the union of `self` and `other`.
    ///
    /// An element is in the result if it is in `self` _or_ if it is in `other`.
    #[trusted]
    #[logic]
    #[creusot::builtins = "set.Fset.union"]
    pub fn union(self, other: Self) -> Self {
        let _ = other;
        dead
    }

    /// Returns `true` if every element of `self` is in `other`.
    #[trusted]
    #[predicate]
    #[creusot::builtins = "set.Fset.subset"]
    pub fn is_subset(self, other: Self) -> bool {
        let _ = other;
        dead
    }

    /// Returns `true` if every element of `other` is in `self`.
    #[open]
    #[predicate]
    #[why3::attr = "inline:trivial"]
    pub fn is_superset(self, other: Self) -> bool {
        Self::is_subset(other, self)
    }

    /// Returns the number of elements in the set, also called its length.
    #[trusted]
    #[logic]
    #[creusot::builtins = "set.Fset.cardinal"]
    pub fn len(self) -> Int {
        dead
    }

    /// Get an arbitrary element of the set.
    ///
    /// # Returns
    ///
    /// - If the set is nonempty, the result is guaranteed to be in the set
    /// - If the set is empty, the result is unspecified
    #[trusted]
    #[logic]
    #[creusot::builtins = "set.Fset.pick"]
    pub fn peek(self) -> T
    where
        T: Sized,
    {
        dead
    }

    /// Extensional equality
    ///
    /// Returns `true` if `self` and `other` contain exactly the same elements.
    ///
    /// This is in fact equivalent with normal equality.
    // FIXME: remove `trusted`
    #[trusted]
    #[open]
    #[predicate]
    #[ensures(result ==> self == other)]
    pub fn ext_eq(self, other: Self) -> bool
    where
        T: Sized,
    {
        pearlite! {
            forall <e: T> self.contains(e) == other.contains(e)
        }
    }
}

/// Ghost definitions
impl<T: ?Sized> FSet<T> {
    /// Create a new, empty set on the ghost heap.
    #[trusted]
    #[pure]
    #[ensures(result.is_empty())]
    #[allow(unreachable_code)]
    pub fn new() -> GhostBox<Self> {
        ghost!(panic!())
    }

    /// Returns the number of elements in the set.
    ///
    /// If you need to get the length in pearlite, consider using [`len`](Self::len).
    ///
    /// # Example
    /// ```rust,creusot
    /// use creusot_contracts::{logic::FSet, *};
    ///
    /// let mut set = FSet::new();
    /// ghost! {
    ///     let len1 = set.len_ghost();
    ///     set.insert_ghost(1);
    ///     set.insert_ghost(2);
    ///     set.insert_ghost(1);
    ///     let len2 = set.len_ghost();
    ///     proof_assert!(len1 == 0);
    ///     proof_assert!(len2 == 2);
    /// };
    /// ```
    #[trusted]
    #[pure]
    #[ensures(result == self.len())]
    pub fn len_ghost(&self) -> Int {
        panic!()
    }

    /// Returns true if the set contains the specified value.
    ///
    /// # Example
    /// ```rust,creusot
    /// use creusot_contracts::{logic::FSet, *};
    ///
    /// let mut set = FSet::new();
    /// ghost! {
    ///     set.insert_ghost(1);
    ///     let (b1, b2) = (set.contains_ghost(&1), set.contains_ghost(&2));
    ///     proof_assert!(b1);
    ///     proof_assert!(!b2);
    /// };
    /// ```
    #[pure]
    #[trusted]
    #[ensures(result == self.contains(*value))]
    pub fn contains_ghost(&self, value: &T) -> bool {
        let _ = value;
        panic!()
    }

    /// Adds a value to the set.
    ///
    /// Returns whether the value was newly inserted. That is:
    /// - If the set did not previously contain this value, `true` is returned.
    /// - If the set already contained this value, `false` is returned, and the set is
    ///   not modified: original value is not replaced, and the value passed as argument
    ///   is dropped.
    ///
    /// # Example
    /// ```rust,creusot
    /// use creusot_contracts::{logic::FSet, *};
    ///
    /// let mut set = FSet::new();
    /// ghost! {
    ///     let res1 = set.insert_ghost(42);
    ///     proof_assert!(res1);
    ///     proof_assert!(set.contains(42i32));
    ///
    ///     let res2 = set.insert_ghost(41);
    ///     let res3 = set.insert_ghost(42);
    ///     proof_assert!(res2);
    ///     proof_assert!(!res3);
    ///     proof_assert!(set.len() == 2);
    /// };
    /// ```
    #[trusted]
    #[pure]
    #[ensures(^self == (*self).insert(value))]
    #[ensures(result == !(*self).contains(value))]
    pub fn insert_ghost(&mut self, value: T) -> bool
    where
        T: Sized,
    {
        let _ = value;
        panic!()
    }

    /// Same as [`Self::insert_ghost`], but for unsized values.
    #[trusted]
    #[pure]
    #[ensures(^self == (*self).insert(*value))]
    #[ensures(result == !(*self).contains(*value))]
    pub fn insert_ghost_unsized(&mut self, value: Box<T>) -> bool {
        let _ = value;
        panic!()
    }

    /// Removes a value from the set. Returns whether the value was present in the set.
    ///
    /// # Example
    /// ```rust,creusot
    /// use creusot_contracts::{logic::FSet, *};
    ///
    /// let mut set = FSet::new();
    /// let res = ghost! {
    ///     set.insert_ghost(1);
    ///     let res1 = set.remove_ghost(&1);
    ///     let res2 = set.remove_ghost(&1);
    ///     proof_assert!(res1 && !res2);
    /// };
    /// ```
    #[trusted]
    #[pure]
    #[ensures(^self == (*self).remove(*value))]
    #[ensures(result == (*self).contains(*value))]
    pub fn remove_ghost(&mut self, value: &T) -> bool {
        let _ = value;
        panic!()
    }
}
