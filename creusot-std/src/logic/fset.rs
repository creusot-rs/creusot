#[cfg(creusot)]
use crate::resolve::structural_resolve;
use crate::{logic::Mapping, prelude::*};
use core::marker::PhantomData;

/// A finite set type usable in pearlite and `ghost!` blocks.
///
/// If you need an infinite set, see [`Set`](super::Set).
///
/// # Ghost
///
/// Since [`std::collections::HashSet`] and
/// [`std::collections::BTreeSet`] have finite
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
#[opaque]
#[builtin("set.Fset.fset")]
pub struct FSet<T>(PhantomData<T>);

impl<T> FSet<T> {
    /// Returns the empty set.
    #[logic]
    #[builtin("set.Fset.empty", ascription)]
    pub fn empty() -> Self {
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
    #[builtin("set.Fset.mem")]
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
    #[builtin("set.Fset.add")]
    pub fn add(_: T, _: Self) -> Self {
        dead
    }

    /// Returns `true` if the set contains no elements.
    #[logic]
    #[builtin("set.Fset.is_empty")]
    pub fn is_empty(self) -> bool {
        dead
    }

    /// Returns a new set, where `e` is no longer present.
    #[logic(open, inline)]
    pub fn remove(self, e: T) -> Self {
        Self::rem(e, self)
    }

    /// [`Self::remove`], but with the order of arguments flipped.
    ///
    /// This is how the function is defined in why3.
    #[doc(hidden)]
    #[logic]
    #[builtin("set.Fset.remove")]
    pub fn rem(_: T, _: Self) -> Self {
        dead
    }

    /// Returns a new set, which is the union of `self` and `other`.
    ///
    /// An element is in the result if it is in `self` _or_ if it is in `other`.
    #[logic]
    #[builtin("set.Fset.union")]
    pub fn union(self, other: Self) -> Self {
        let _ = other;
        dead
    }

    /// Returns a new set, which is the union of `self` and `other`.
    ///
    /// An element is in the result if it is in `self` _or_ if it is in `other`.
    #[logic]
    #[builtin("set.Fset.inter")]
    pub fn intersection(self, other: Self) -> Self {
        let _ = other;
        dead
    }

    /// Returns a new set, which is the difference of `self` with `other`.
    ///
    /// An element is in the result if and only if it is in `self` but not in `other`.
    #[logic]
    #[builtin("set.Fset.diff")]
    pub fn difference(self, other: Self) -> Self {
        let _ = other;
        dead
    }

    /// Returns `true` if every element of `self` is in `other`.
    #[logic]
    #[builtin("set.Fset.subset")]
    pub fn is_subset(self, other: Self) -> bool {
        let _ = other;
        dead
    }

    /// Returns `true` if every element of `other` is in `self`.
    #[logic(open, inline)]
    pub fn is_superset(self, other: Self) -> bool {
        Self::is_subset(other, self)
    }

    /// Returns `true` if `self` and `other` are disjoint.
    #[logic]
    #[builtin("set.Fset.disjoint")]
    pub fn disjoint(self, other: Self) -> bool {
        let _ = other;
        dead
    }

    /// Returns the number of elements in the set, also called its length.
    #[logic]
    #[builtin("set.Fset.cardinal")]
    pub fn len(self) -> Int {
        dead
    }

    /// Get an arbitrary element of the set.
    ///
    /// # Returns
    ///
    /// - If the set is nonempty, the result is guaranteed to be in the set
    /// - If the set is empty, the result is unspecified
    #[logic]
    #[builtin("set.Fset.pick")]
    pub fn peek(self) -> T {
        dead
    }

    /// Extensional equality
    ///
    /// Returns `true` if `self` and `other` contain exactly the same elements.
    ///
    /// This is in fact equivalent with normal equality.
    #[logic(open)]
    #[ensures(result == (self == other))]
    pub fn ext_eq(self, other: Self) -> bool {
        pearlite! {
            forall <e: T> self.contains(e) == other.contains(e)
        }
    }

    /// Returns the set containing only `x`.
    #[logic(open)]
    #[ensures(forall<y: T> result.contains(y) == (x == y))]
    pub fn singleton(x: T) -> Self {
        FSet::empty().insert(x)
    }

    /// Returns the union of sets `f(t)` over all `t: T`.
    #[logic(open)]
    #[ensures(forall<y: U> result.contains(y) == exists<x: T> self.contains(x) && f.get(x).contains(y))]
    #[variant(self.len())]
    pub fn unions<U>(self, f: Mapping<T, FSet<U>>) -> FSet<U> {
        if self.len() == 0 {
            FSet::empty()
        } else {
            let x = self.peek();
            f.get(x).union(self.remove(x).unions(f))
        }
    }

    /// Flipped `map`.
    #[logic]
    #[builtin("set.Fset.map")]
    pub fn fmap<U>(_: Mapping<T, U>, _: Self) -> FSet<U> {
        dead
    }

    /// Returns the image of a set by a function.
    #[logic(open)]
    pub fn map<U>(self, f: Mapping<T, U>) -> FSet<U> {
        FSet::fmap(f, self)
    }

    /// Returns the subset of elements of `self` which satisfy the predicate `f`.
    #[logic]
    #[builtin("set.Fset.filter")]
    pub fn filter(self, f: Mapping<T, bool>) -> Self {
        let _ = f;
        dead
    }

    /// Returns the set of sequences whose head is in `s` and whose tail is in `ss`.
    #[logic(open)]
    #[ensures(forall<xs: Seq<T>> result.contains(xs) == (0 < xs.len() && s.contains(xs[0]) && ss.contains(xs.tail())))]
    pub fn cons(s: FSet<T>, ss: FSet<Seq<T>>) -> FSet<Seq<T>> {
        proof_assert!(forall<x:T, xs: Seq<T>> xs.push_front(x).tail() == xs);
        proof_assert!(forall<xs: Seq<T>> 0 < xs.len() ==> xs.tail().push_front(xs[0]) == xs);
        s.unions(|x| ss.map(|xs: Seq<_>| xs.push_front(x)))
    }

    /// Returns the set of concatenations of a sequence in `s` and a sequence in `t`.
    #[logic(open)]
    #[ensures(forall<xs: Seq<T>> result.contains(xs) == (exists<ys: Seq<T>, zs: Seq<T>> s.contains(ys) && t.contains(zs) && xs == ys.concat(zs)))]
    pub fn concat(s: FSet<Seq<T>>, t: FSet<Seq<T>>) -> FSet<Seq<T>> {
        s.unions(|ys: Seq<_>| t.map(|zs| ys.concat(zs)))
    }

    /// Returns the set of sequences of length `n` whose elements are in `self`.
    #[logic(open)]
    #[requires(n >= 0)]
    #[ensures(forall<xs: Seq<T>> result.contains(xs) == (xs.len() == n && forall<x: T> xs.contains(x) ==> self.contains(x)))]
    #[variant(n)]
    pub fn replicate(self, n: Int) -> FSet<Seq<T>> {
        pearlite! {
            if n == 0 {
                proof_assert! { forall<xs: Seq<T>> xs.len() == 0 ==> xs == Seq::empty() };
                FSet::singleton(Seq::empty())
            } else {
                proof_assert! { forall<xs: Seq<T>, i> 0 < i && i < xs.len() ==> xs[i] == xs.tail()[i-1] };
                FSet::cons(self, self.replicate(n - 1))
            }
        }
    }

    /// Returns the set of sequences of length at most `n` whose elements are in `self`.
    #[logic(open)]
    #[requires(n >= 0)]
    #[ensures(forall<xs: Seq<T>> result.contains(xs) == (xs.len() <= n && forall<x: T> xs.contains(x) ==> self.contains(x)))]
    #[variant(n)]
    pub fn replicate_up_to(self, n: Int) -> FSet<Seq<T>> {
        pearlite! {
            if n == 0 {
                proof_assert! { forall<xs: Seq<T>> xs.len() == 0 ==> xs == Seq::empty() };
                FSet::singleton(Seq::empty())
            } else {
                self.replicate_up_to(n - 1).union(self.replicate(n))
            }
        }
    }
}

impl FSet<Int> {
    /// Return the interval of integers in `[i, j)`.
    #[logic(open)]
    #[builtin("set.FsetInt.interval")]
    pub fn interval(i: Int, j: Int) -> FSet<Int> {
        let _ = (i, j);
        dead
    }
}

/// Ghost definitions
impl<T> FSet<T> {
    /// Create a new, empty set on the ghost heap.
    #[trusted]
    #[check(ghost)]
    #[ensures(result.is_empty())]
    #[allow(unreachable_code)]
    pub fn new() -> Ghost<Self> {
        Ghost::conjure()
    }

    /// Returns the number of elements in the set.
    ///
    /// If you need to get the length in pearlite, consider using [`len`](Self::len).
    ///
    /// # Example
    /// ```rust,creusot
    /// use creusot_std::{logic::FSet, prelude::*};
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
    #[check(ghost)]
    #[ensures(result == self.len())]
    pub fn len_ghost(&self) -> Int {
        panic!()
    }

    /// Returns true if the set contains the specified value.
    ///
    /// # Example
    /// ```rust,creusot
    /// use creusot_std::{logic::FSet, prelude::*};
    ///
    /// let mut set = FSet::new();
    /// ghost! {
    ///     set.insert_ghost(1);
    ///     let (b1, b2) = (set.contains_ghost(&1), set.contains_ghost(&2));
    ///     proof_assert!(b1);
    ///     proof_assert!(!b2);
    /// };
    /// ```
    #[trusted]
    #[check(ghost)]
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
    /// use creusot_std::{logic::FSet, prelude::*};
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
    #[check(ghost)]
    #[ensures(^self == (*self).insert(value))]
    #[ensures(result == !(*self).contains(value))]
    pub fn insert_ghost(&mut self, value: T) -> bool {
        let _ = value;
        panic!()
    }

    /// Removes a value from the set. Returns whether the value was present in the set.
    ///
    /// # Example
    /// ```rust,creusot
    /// use creusot_std::{logic::FSet, prelude::*};
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
    #[check(ghost)]
    #[ensures(^self == (*self).remove(*value))]
    #[ensures(result == (*self).contains(*value))]
    pub fn remove_ghost(&mut self, value: &T) -> bool {
        let _ = value;
        panic!()
    }

    /// Clears the set, removing all values.
    ///
    /// # Example
    /// ```rust,creusot
    /// use creusot_std::{prelude::*, logic::FSet};
    ///
    /// let mut s = FSet::new();
    /// ghost! {
    ///     s.insert_ghost(1);
    ///     s.insert_ghost(2);
    ///     s.insert_ghost(3);
    ///     s.clear_ghost();
    ///     proof_assert!(s == FSet::empty());
    /// };
    /// ```
    #[trusted]
    #[check(ghost)]
    #[ensures(^self == Self::empty())]
    pub fn clear_ghost(&mut self) {}
}

impl<T: Clone + Copy> Clone for FSet<T> {
    #[trusted]
    #[check(ghost)]
    #[ensures(result == *self)]
    fn clone(&self) -> Self {
        *self
    }
}

// Having `Copy` guarantees that the operation is pure, even if we decide to change the definition of `Clone`.
impl<T: Clone + Copy> Copy for FSet<T> {}

impl<T> Invariant for FSet<T> {
    #[logic(open, prophetic, inline)]
    #[creusot::trusted_trivial_if_param_trivial]
    fn invariant(self) -> bool {
        pearlite! { forall<x: T> self.contains(x) ==> inv(x) }
    }
}
impl<T> Resolve for FSet<T> {
    #[logic(open, prophetic)]
    #[creusot::trusted_trivial_if_param_trivial]
    fn resolve(self) -> bool {
        pearlite! { forall<x: T> self.contains(x) ==> resolve(x) }
    }

    #[trusted]
    #[logic(open(self), prophetic)]
    #[requires(structural_resolve(self))]
    #[ensures(self.resolve())]
    fn resolve_coherence(self) {}
}

// Properties
// TODO: replace quantification with parameters, and move to impl block.

/// Distributivity of `unions` over `union`.
#[logic(open)]
#[ensures(forall<s1: FSet<T>, s2: FSet<T>, f: Mapping<T, FSet<U>>> s1.union(s2).unions(f) == s1.unions(f).union(s2.unions(f)))]
#[ensures(forall<s: FSet<T>, f: Mapping<T, FSet<U>>, g: Mapping<T, FSet<U>>>
    s.unions(|x| f.get(x).union(g.get(x))) == s.unions(f).union(s.unions(g)))]
pub fn unions_union<T, U>() {}

/// Distributivity of `map` over `union`.
#[logic(open)]
#[ensures(forall<s: FSet<T>, t: FSet<T>, f: Mapping<T, U>> s.union(t).map(f) == s.map(f).union(t.map(f)))]
pub fn map_union<T, U>() {}

/// Distributivity of `concat` over `union`.
#[logic(open)]
#[ensures(forall<s1: FSet<Seq<T>>, s2: FSet<Seq<T>>, t: FSet<Seq<T>>>
    FSet::concat(s1.union(s2), t) == FSet::concat(s1, t).union(FSet::concat(s2, t)))]
#[ensures(forall<s: FSet<Seq<T>>, t1: FSet<Seq<T>>, t2: FSet<Seq<T>>>
    FSet::concat(s, t1.union(t2)) == FSet::concat(s, t1).union(FSet::concat(s, t2)))]
pub fn concat_union<T>() {}

/// Distributivity of `cons` over `union`.
#[logic(open)]
#[ensures(forall<s: FSet<T>, t: FSet<Seq<T>>, u: FSet<Seq<T>>> FSet::concat(FSet::cons(s, t), u) == FSet::cons(s, FSet::concat(t, u)))]
pub fn cons_concat<T>() {
    proof_assert! { forall<x: T, xs: Seq<T>, ys: Seq<T>> xs.push_front(x).concat(ys) == xs.concat(ys).push_front(x) };
    proof_assert! { forall<x: T, ys: Seq<T>> ys.push_front(x).tail() == ys };
    proof_assert! { forall<ys: Seq<T>> 0 < ys.len() ==> ys == ys.tail().push_front(ys[0]) };
}

/// Distributivity of `replicate` over `union`.
#[logic(open)]
#[requires(0 <= n && 0 <= m)]
#[ensures(s.replicate(n + m) == FSet::concat(s.replicate(n), s.replicate(m)))]
#[variant(n)]
pub fn concat_replicate<T>(n: Int, m: Int, s: FSet<T>) {
    pearlite! {
        if n == 0 {
            concat_empty(s.replicate(m));
        } else {
            cons_concat::<T>();
            concat_replicate(n - 1, m, s);
        }
    }
}

/// The neutral element of `FSet::concat` is `FSet::singleton(Seq::empty())`.
#[logic(open)]
#[ensures(FSet::concat(FSet::singleton(Seq::empty()), s) == s)]
#[ensures(FSet::concat(s, FSet::singleton(Seq::empty())) == s)]
pub fn concat_empty<T>(s: FSet<Seq<T>>) {
    proof_assert! { forall<xs: Seq<T>> xs.concat(Seq::empty()) == xs };
    proof_assert! { forall<xs: Seq<T>> Seq::empty().concat(xs) == xs };
}

/// An equation relating `s.replicate_up_to(m)` and `s.replicate_up_to(n)`.
#[logic(open)]
#[requires(0 <= n && n < m)]
#[ensures(s.replicate_up_to(m) == s.replicate_up_to(n).union(
    FSet::concat(s.replicate(n + 1), s.replicate_up_to(m - n - 1))))]
#[variant(m)]
pub fn concat_replicate_up_to<T>(n: Int, m: Int, s: FSet<T>) {
    pearlite! {
        if n + 1 == m {
            concat_empty(s.replicate(n + 1));
        } else {
            concat_union::<T>();
            concat_replicate(n, m - n - 1, s);
            concat_replicate_up_to(n, m - 1, s);
        }
    }
}
