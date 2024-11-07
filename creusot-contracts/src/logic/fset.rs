use crate::*;

/// A Set type usable in pearlite and `ghost!` blocks.
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
    #[cfg(creusot)]
    #[trusted]
    #[creusot::builtins = "set.Fset.empty"]
    pub const EMPTY: Self = { FSet(std::marker::PhantomData) };

    #[open]
    #[predicate]
    #[why3::attr = "inline:trivial"]
    pub fn contains(self, e: T) -> bool {
        Self::mem(e, self)
    }

    #[doc(hidden)]
    #[trusted]
    #[logic]
    #[creusot::builtins = "set.Fset.mem"]
    pub fn mem(_: T, _: Self) -> bool {
        dead
    }

    #[open]
    #[logic]
    #[why3::attr = "inline:trivial"]
    pub fn insert(self, e: T) -> Self {
        Self::add(e, self)
    }

    #[doc(hidden)]
    #[trusted]
    #[logic]
    #[creusot::builtins = "set.Fset.add"]
    pub fn add(_: T, _: Self) -> Self {
        dead
    }

    #[trusted]
    #[predicate]
    #[creusot::builtins = "set.Fset.is_empty"]
    pub fn is_empty(self) -> bool {
        dead
    }

    #[open]
    #[logic]
    #[why3::attr = "inline:trivial"]
    pub fn remove(self, a: T) -> Self {
        Self::rem(a, self)
    }

    #[doc(hidden)]
    #[trusted]
    #[logic]
    #[creusot::builtins = "set.Fset.remove"]
    pub fn rem(_: T, _: Self) -> Self {
        dead
    }

    #[trusted]
    #[logic]
    #[creusot::builtins = "set.Fset.union"]
    pub fn union(self, _: Self) -> Self {
        dead
    }

    #[trusted]
    #[predicate]
    #[creusot::builtins = "set.Fset.subset"]
    pub fn is_subset(self, _: Self) -> bool {
        dead
    }

    #[open]
    #[predicate]
    #[why3::attr = "inline:trivial"]
    pub fn is_superset(self, other: Self) -> bool {
        Self::is_subset(other, self)
    }

    #[trusted]
    #[logic]
    #[creusot::builtins = "set.Fset.cardinal"]
    pub fn len(self) -> Int {
        dead
    }

    #[trusted]
    #[logic]
    #[creusot::builtins = "set.Fset.pick"]
    pub fn peek(self) -> T
    where
        T: Sized,
    {
        dead
    }

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
        ghost!(loop {})
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
