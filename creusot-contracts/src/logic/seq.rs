use crate::{
    ghost::Plain,
    logic::{Mapping, ops::IndexLogic},
    *,
};

/// A type of sequence usable in pearlite and `ghost!` blocks.
///
/// # Logic
///
/// This type is (in particular) the logical representation of a [`Vec`]. This can be
/// accessed via its [view](crate::View) (The `@` operator).
///
/// ```rust,creusot
/// # use creusot_contracts::*;
/// #[logic]
/// fn get_model<T>(v: Vec<T>) -> Seq<T> {
///     pearlite!(v@)
/// }
/// ```
///
/// # Ghost
///
/// Since [`Vec`] have finite capacity, this could cause some issues in ghost code:
/// ```rust,creusot,compile_fail
/// ghost! {
///     let mut v = Vec::new();
///     for _ in 0..=usize::MAX as u128 + 1 {
///         v.push(0); // cannot fail, since we are in a ghost block
///     }
///     proof_assert!(v@.len() <= usize::MAX@); // by definition
///     proof_assert!(v@.len() > usize::MAX@); // uh-oh
/// }
/// ```
///
/// This type is designed for this use-case, with no restriction on the capacity.
#[trusted]
#[cfg_attr(creusot, creusot::builtins = "seq.Seq.seq")]
pub struct Seq<T>(std::marker::PhantomData<T>);

/// Logical definitions
impl<T> Seq<T> {
    /// Returns the empty sequence.
    #[logic]
    #[trusted]
    #[creusot::builtins = "seq.Seq.empty"]
    #[creusot::builtins_ascription]
    pub fn empty() -> Self {
        dead
    }

    /// Create a new sequence in pearlite.
    ///
    /// The new sequence will be of length `n`, and will contain `mapping[i]` at index `i`.
    ///
    /// # Example
    ///
    /// ```
    /// # use creusot_contracts::*;
    /// let s = snapshot!(Seq::create(5, |i| i + 1));
    /// proof_assert!(s.len() == 5);
    /// proof_assert!(forall<i> 0 <= i && i < 5 ==> s[i] == i + 1);
    /// ```
    #[trusted]
    #[logic]
    #[creusot::builtins = "seq.Seq.create"]
    pub fn create(n: Int, mapping: Mapping<Int, T>) -> Self {
        let _ = n;
        let _ = mapping;
        dead
    }

    /// Returns the value at index `ix`.
    ///
    /// If `ix` is out of bounds, return `None`.
    #[logic]
    #[open]
    pub fn get(self, ix: Int) -> Option<T> {
        if 0 <= ix && ix < self.len() { Some(self.index_logic(ix)) } else { None }
    }

    /// Returns the value at index `ix`.
    ///
    /// If `ix` is out of bounds, the returned value is meaningless.
    ///
    /// You should prefer using the indexing operator `s[ix]`.
    ///
    /// # Example
    ///
    /// ```
    /// # use creusot_contracts::*;
    /// let s = snapshot!(Seq::singleton(2));
    /// proof_assert!(s.index_logic_unsized(0) == 2);
    /// proof_assert!(s[0] == 2); // prefer this
    /// ```
    #[trusted]
    #[logic]
    #[creusot::builtins = "seq.Seq.get"]
    pub fn index_logic_unsized(self, ix: Int) -> Box<T> {
        let _ = ix;
        dead
    }

    /// Returns the subsequence between indices `start` and `end`.
    ///
    /// If either `start` or `end` are out of bounds, the result is meaningless.
    ///
    /// # Example
    ///
    /// ```
    /// # use creusot_contracts::*;
    /// let subs = snapshot! {
    ///     let s: Seq<Int> = Seq::create(10, |i| i);
    ///     s.subsequence(2, 5)
    /// };
    /// proof_assert!(subs.len() == 3);
    /// proof_assert!(subs[0] == 2 && subs[1] == 3 && subs[2] == 4);
    /// ```
    #[trusted]
    #[logic]
    #[creusot::builtins = "seq.Seq.([..])"]
    pub fn subsequence(self, start: Int, end: Int) -> Self {
        let _ = start;
        let _ = end;
        dead
    }

    /// Create a sequence containing one element.
    ///
    /// # Example
    ///
    /// ```
    /// # use creusot_contracts::*;
    /// let s = snapshot!(Seq::singleton(42));
    /// proof_assert!(s.len() == 1);
    /// proof_assert!(s[0] == 42);
    /// ```
    #[trusted]
    #[logic]
    #[creusot::builtins = "seq.Seq.singleton"]
    pub fn singleton(value: T) -> Self {
        let _ = value;
        dead
    }

    /// Returns the sequence without its first element.
    ///
    /// If the sequence is empty, the result is meaningless.
    ///
    /// # Example
    ///
    /// ```
    /// # use creusot_contracts::*;
    /// let s = snapshot!(Seq::singleton(5).push_back(10).push_back(15));
    /// proof_assert!(s.tail() == Seq::singleton(10).push_back(15));
    /// proof_assert!(s.tail().tail() == Seq::singleton(15));
    /// proof_assert!(s.tail().tail().tail() == Seq::empty());
    /// ```
    #[logic]
    #[open]
    pub fn tail(self) -> Self {
        self.subsequence(1, self.len())
    }

    /// Returns the number of elements in the sequence, also referred to as its 'length'.
    ///
    /// # Example
    ///
    /// ```
    /// # use creusot_contracts::*;
    /// #[requires(v@.len() > 0)]
    /// fn f<T>(v: Vec<T>) { /* ... */ }
    /// ```
    #[trusted]
    #[logic]
    #[creusot::builtins = "seq.Seq.length"]
    pub fn len(self) -> Int {
        dead
    }

    /// Returns a new sequence, where the element at index `ix` has been replaced by `x`.
    ///
    /// If `ix` is out of bounds, the result is meaningless.
    ///
    /// # Example
    ///
    /// ```
    /// # use creusot_contracts::*;
    /// let s = snapshot!(Seq::create(2, |_| 0));
    /// let s2 = snapshot!(s.set(1, 3));
    /// proof_assert!(s2[0] == 0);
    /// proof_assert!(s2[1] == 3);
    /// ```
    #[trusted]
    #[logic]
    #[creusot::builtins = "seq.Seq.set"]
    pub fn set(self, ix: Int, x: T) -> Self {
        let _ = ix;
        let _ = x;
        dead
    }

    /// Extensional equality
    ///
    /// Returns `true` if `self` and `other` have the same length, and contain the same
    /// elements at the same indices.
    ///
    /// This is in fact equivalent with normal equality.
    #[trusted]
    #[logic]
    #[creusot::builtins = "seq.Seq.(==)"]
    pub fn ext_eq(self, other: Self) -> bool {
        let _ = other;
        dead
    }

    // internal wrapper to match the order of arguments of Seq.cons
    #[doc(hidden)]
    #[trusted]
    #[logic]
    #[creusot::builtins = "seq.Seq.cons"]
    pub fn cons(_: T, _: Self) -> Self {
        dead
    }

    /// Returns a new sequence, where `x` has been prepended to `self`.
    ///
    /// # Example
    ///
    /// ```
    /// let s = snapshot!(Seq::singleton(1));
    /// let s2 = snapshot!(s.push_front(2));
    /// proof_assert!(s2[0] == 2);
    /// proof_assert!(s2[1] == 1);
    /// ```
    #[logic]
    #[open]
    #[creusot::why3_attr = "inline:trivial"]
    pub fn push_front(self, x: T) -> Self {
        Self::cons(x, self)
    }

    /// Returns a new sequence, where `x` has been appended to `self`.
    ///
    /// # Example
    ///
    /// ```
    /// let s = snapshot!(Seq::singleton(1));
    /// let s2 = snapshot!(s.push_back(2));
    /// proof_assert!(s2[0] == 1);
    /// proof_assert!(s2[1] == 2);
    /// ```
    #[trusted]
    #[logic]
    #[creusot::builtins = "seq.Seq.snoc"]
    pub fn push_back(self, x: T) -> Self {
        let _ = x;
        dead
    }

    /// Returns a new sequence, made of the concatenation of `self` and `other`.
    ///
    /// # Example
    ///
    /// ```
    /// # use creusot_contracts::*;
    /// let s1 = snapshot!(Seq::singleton(1));
    /// let s2 = snapshot!(Seq::create(2, |i| i));
    /// let s = snapshot!(s1.concat(s2));
    /// proof_assert!(s[0] == 1);
    /// proof_assert!(s[1] == 0);
    /// proof_assert!(s[2] == 1);
    /// ```
    #[trusted]
    #[logic]
    #[creusot::builtins = "seq.Seq.(++)"]
    pub fn concat(self, other: Self) -> Self {
        let _ = other;
        dead
    }

    #[logic]
    #[open]
    #[variant(self.len())]
    pub fn flat_map<U>(self, other: Mapping<T, Seq<U>>) -> Seq<U> {
        if self.len() == 0 {
            Seq::empty()
        } else {
            other.get(*self.index_logic_unsized(0)).concat(self.tail().flat_map(other))
        }
    }

    /// Returns a new sequence, which is `self` in reverse order.
    ///
    /// # Example
    ///
    /// ```
    /// # use creusot_contracts::*;
    /// let s = snapshot!(Seq::create(3, |i| i));
    /// let s2 = snapshot!(s.reverse());
    /// proof_assert!(s2[0] == 2);
    /// proof_assert!(s2[1] == 1);
    /// proof_assert!(s2[2] == 0);
    /// ```
    #[trusted]
    #[logic]
    #[creusot::builtins = "seq.Reverse.reverse"]
    pub fn reverse(self) -> Self {
        dead
    }

    /// Returns `true` if `other` is a permutation of `self`.
    #[logic]
    #[open]
    pub fn permutation_of(self, other: Self) -> bool {
        self.permut(other, 0, self.len())
    }

    /// Returns `true` if:
    /// - `self` and `other` have the same length
    /// - `start` and `end` are in bounds (between `0` and `self.len()` included)
    /// - Every element of `self` between `start` (included) and `end` (excluded) can
    ///   also be found in `other` between `start` and `end`, and vice-versa
    #[trusted]
    #[logic]
    #[creusot::builtins = "seq.Permut.permut"]
    pub fn permut(self, other: Self, start: Int, end: Int) -> bool {
        let _ = other;
        let _ = start;
        let _ = end;
        dead
    }

    /// Returns `true` if:
    /// - `self` and `other` have the same length
    /// - `i` and `j` are in bounds (between `0` and `self.len()` excluded)
    /// - `other` is equal to `self` where the elements at `i` and `j` are swapped
    #[trusted]
    #[logic]
    #[creusot::builtins = "seq.Permut.exchange"]
    pub fn exchange(self, other: Self, i: Int, j: Int) -> bool {
        let _ = other;
        let _ = i;
        let _ = j;
        dead
    }

    /// Returns `true` if there is an index `i` such that `self[i] == x`.
    #[open]
    #[logic]
    pub fn contains(self, x: T) -> bool {
        pearlite! { exists<i> 0 <= i &&  i < self.len() && self[i] == x }
    }

    /// Returns `true` if `self` is sorted between `start` and `end`.
    #[open]
    #[logic]
    pub fn sorted_range(self, start: Int, end: Int) -> bool
    where
        T: OrdLogic,
    {
        pearlite! {
            forall<i, j> start <= i && i <= j && j < end ==> self[i] <= self[j]
        }
    }

    /// Returns `true` if `self` is sorted.
    #[open]
    #[logic]
    pub fn sorted(self) -> bool
    where
        T: OrdLogic,
    {
        self.sorted_range(0, self.len())
    }

    #[open]
    #[logic]
    #[ensures(forall<a: Seq<T>, b: Seq<T>, x>
        a.concat(b).contains(x) == a.contains(x) || b.contains(x))]
    pub fn concat_contains() {}
}

impl<T> Seq<Seq<T>> {
    #[open]
    #[logic]
    #[variant(self.len())]
    pub fn flatten(self) -> Seq<T> {
        if self.len() == 0 {
            Seq::empty()
        } else {
            self.index_logic_unsized(0).concat(self.tail().flatten())
        }
    }
}

impl<T> Seq<&T> {
    /// Convert `Seq<&T>` to `Seq<T>`.
    ///
    /// This is simply a utility method, because `&T` is equivalent to `T` in pearlite.
    #[logic]
    #[trusted]
    #[creusot::builtins = "identity"]
    pub fn to_owned_seq(self) -> Seq<T> {
        dead
    }
}

impl<T> IndexLogic<Int> for Seq<T> {
    type Item = T;

    #[logic]
    #[trusted]
    #[creusot::builtins = "seq.Seq.get"]
    fn index_logic(self, _: Int) -> Self::Item {
        dead
    }
}

/// Ghost definitions
impl<T> Seq<T> {
    /// Constructs a new, empty `Seq<T>`.
    ///
    /// This can only be manipulated in the ghost world, and as such is wrapped in [`Ghost`].
    ///
    /// # Example
    ///
    /// ```rust,creusot
    /// use creusot_contracts::{proof_assert, Seq};
    /// let ghost_seq = Seq::<i32>::new();
    /// proof_assert!(seq == Seq::create());
    /// ```
    #[trusted]
    #[check(ghost)]
    #[ensures(*result == Self::empty())]
    #[allow(unreachable_code)]
    pub fn new() -> Ghost<Self> {
        Ghost::conjure()
    }

    /// Returns the number of elements in the sequence, also referred to as its 'length'.
    ///
    /// If you need to get the length in pearlite, consider using [`len`](Self::len).
    ///
    /// # Example
    /// ```rust,creusot
    /// use creusot_contracts::{ghost, proof_assert, Seq};
    ///
    /// let mut s = Seq::new();
    /// ghost! {
    ///     s.push_back_ghost(1);
    ///     s.push_back_ghost(2);
    ///     s.push_back_ghost(3);
    ///     let len = s.len_ghost();
    ///     proof_assert!(len == 3);
    /// };
    /// ```
    #[trusted]
    #[check(ghost)]
    #[ensures(result == self.len())]
    pub fn len_ghost(&self) -> Int {
        panic!()
    }

    /// Returns `true` if the sequence is empty.
    ///
    /// # Example
    ///
    /// ```rust,creusot
    /// use creusot_contracts::*;
    /// #[check(ghost)]
    /// #[requires(s.len() == 0)]
    /// pub fn foo(mut s: Seq<i32>) {
    ///     assert!(s.is_empty_ghost());
    ///     s.push_back_ghost(1i32);
    ///     assert!(!s.is_empty_ghost());
    /// }
    /// ghost! {
    ///     foo(Seq::new().into_inner())
    /// };
    /// ```
    #[trusted]
    #[check(ghost)]
    #[ensures(result == (self.len() == 0))]
    pub fn is_empty_ghost(&self) -> bool {
        panic!()
    }

    /// Appends an element to the front of a collection.
    ///
    /// # Example
    /// ```rust,creusot
    /// use creusot_contracts::{ghost, proof_assert, Seq};
    ///
    /// let mut s = Seq::new();
    /// ghost! {
    ///     s.push_front_ghost(1);
    ///     s.push_front_ghost(2);
    ///     s.push_front_ghost(3);
    ///     proof_assert!(s[0] == 3i32 && s[1] == 2i32 && s[2] == 1i32);
    /// };
    /// ```
    #[trusted]
    #[check(ghost)]
    #[ensures(^self == self.push_front(x))]
    pub fn push_front_ghost(&mut self, x: T) {
        let _ = x;
        panic!()
    }

    /// Appends an element to the back of a collection.
    ///
    /// # Example
    /// ```rust,creusot
    /// use creusot_contracts::{ghost, proof_assert, Seq};
    ///
    /// let mut s = Seq::new();
    /// ghost! {
    ///     s.push_back_ghost(1);
    ///     s.push_back_ghost(2);
    ///     s.push_back_ghost(3);
    ///     proof_assert!(s[0] == 1i32 && s[1] == 2i32 && s[2] == 3i32);
    /// };
    /// ```
    #[trusted]
    #[check(ghost)]
    #[ensures(^self == self.push_back(x))]
    pub fn push_back_ghost(&mut self, x: T) {
        let _ = x;
        panic!()
    }

    /// Returns a reference to an element at `index` or `None` if `index` is out of bounds.
    ///
    /// # Example
    /// ```rust,creusot
    /// use creusot_contracts::{ghost, Int, proof_assert, Seq};
    ///
    /// let mut s = Seq::new();
    /// ghost! {
    ///     s.push_back_ghost(10);
    ///     s.push_back_ghost(40);
    ///     s.push_back_ghost(30);
    ///     let get1 = s.get_ghost(1int);
    ///     let get2 = s.get_ghost(3int);
    ///     proof_assert!(get1 == Some(&40i32));
    ///     proof_assert!(get2 == None);
    /// };
    /// ```
    #[trusted]
    #[check(ghost)]
    #[ensures(match self.get(index) {
        None => result == None,
        Some(v) => result == Some(&v),
    })]
    pub fn get_ghost(&self, index: Int) -> Option<&T> {
        let _ = index;
        panic!()
    }

    /// Returns a mutable reference to an element at `index` or `None` if `index` is out of bounds.
    ///
    /// # Example
    /// ```rust,creusot
    /// use creusot_contracts::{ghost, Int, proof_assert, Seq};
    ///
    /// let mut s = Seq::new();
    ///
    /// ghost! {
    ///     s.push_back_ghost(0);
    ///     s.push_back_ghost(1);
    ///     s.push_back_ghost(2);
    ///     if let Some(elem) = s.get_mut_ghost(1int) {
    ///         *elem = 42;
    ///     }
    ///     proof_assert!(s[0] == 0i32 && s[1] == 42i32 && s[2] == 2i32);
    /// };
    /// ```
    #[trusted]
    #[check(ghost)]
    #[ensures(match result {
        None => self.get(index) == None && *self == ^self,
        Some(r) => self.get(index) == Some(*r) && ^r == (^self)[index],
    })]
    #[ensures(forall<i> i != index ==> (*self).get(i) == (^self).get(i))]
    #[ensures((*self).len() == (^self).len())]
    pub fn get_mut_ghost(&mut self, index: Int) -> Option<&mut T> {
        let _ = index;
        panic!()
    }

    /// Removes the last element from a vector and returns it, or `None` if it is empty.
    ///
    /// # Example
    /// ```rust,creusot
    /// use creusot_contracts::{ghost, proof_assert, Seq};
    ///
    /// let mut s = Seq::new();
    /// ghost! {
    ///     s.push_back_ghost(1);
    ///     s.push_back_ghost(2);
    ///     s.push_back_ghost(3);
    ///     let popped = s.pop_back_ghost();
    ///     proof_assert!(popped == Some(3i32));
    ///     proof_assert!(s[0] == 1i32 && s[1] == 2i32);
    /// };
    /// ```
    #[trusted]
    #[check(ghost)]
    #[ensures(match result {
        None => *self == Seq::empty() && *self == ^self,
        Some(r) => *self == (^self).push_back(r)
    })]
    pub fn pop_back_ghost(&mut self) -> Option<T> {
        panic!()
    }

    /// Removes the first element from a vector and returns it, or `None` if it is empty.
    ///
    /// # Example
    /// ```rust,creusot
    /// use creusot_contracts::{ghost, proof_assert, Seq};
    ///
    /// let mut s = Seq::new();
    /// ghost! {
    ///     s.push_back_ghost(1);
    ///     s.push_back_ghost(2);
    ///     s.push_back_ghost(3);
    ///     let popped = s.pop_front_ghost();
    ///     proof_assert!(popped == Some(1i32));
    ///     proof_assert!(s[0] == 2i32 && s[1] == 3i32);
    /// };
    /// ```
    #[trusted]
    #[check(ghost)]
    #[ensures(match result {
        None => *self == Seq::empty() && *self == ^self,
        Some(r) => *self == (^self).push_front(r)
    })]
    pub fn pop_front_ghost(&mut self) -> Option<T> {
        panic!()
    }

    /// Clears the sequence, removing all values.
    ///
    /// # Example
    /// ```rust,creusot
    /// use creusot_contracts::{ghost, proof_assert, Seq};
    ///
    /// let mut s = Seq::new();
    /// ghost! {
    ///     s.push_back_ghost(1);
    ///     s.push_back_ghost(2);
    ///     s.push_back_ghost(3);
    ///     s.clear_ghost();
    ///     proof_assert!(s == Seq::empty());
    /// };
    /// ```
    #[trusted]
    #[check(ghost)]
    #[ensures(^self == Self::empty())]
    pub fn clear_ghost(&mut self) {}
}

// Having `Copy` guarantees that the operation is pure, even if we decide to change the definition of `Clone`.
impl<T: Clone + Copy> Clone for Seq<T> {
    #[check(ghost)]
    #[ensures(result == *self)]
    #[trusted]
    fn clone(&self) -> Self {
        *self
    }
}

impl<T: Copy> Copy for Seq<T> {}
#[trusted]
impl<T: Plain> Plain for Seq<T> {}

impl<T> Invariant for Seq<T> {
    #[logic(prophetic)]
    #[open]
    #[creusot::trusted_ignore_structural_inv]
    #[creusot::trusted_is_tyinv_trivial_if_param_trivial]
    fn invariant(self) -> bool {
        pearlite! { forall<i> 0 <= i && i < self.len() ==> inv(self.index_logic_unsized(i)) }
    }
}

#[logic]
#[open]
#[ensures(forall<x: A, f: Mapping<A, Seq<B>>> Seq::singleton(x).flat_map(f) == f.get(x))]
pub fn flat_map_singleton<A, B>() {}

#[logic]
#[open]
#[ensures(forall<x: A, f: Mapping<A, Seq<B>>> xs.push_back(x).flat_map(f) == xs.flat_map(f).concat(f.get(x)))]
#[variant(xs.len())]
pub fn flat_map_push_back<A, B>(xs: Seq<A>) {
    if xs.len() > 0 {
        flat_map_push_back::<A, B>(xs.tail());
        proof_assert! { forall<x: A> xs.tail().push_back(x) == xs.push_back(x).tail() }
    }
}

/// A sequence literal `seq![a, b, c]`.
#[macro_export]
macro_rules! seq {
    ($($items:expr),+) => { creusot_contracts::__stubs::seq_literal(&[$($items),+]) };
    () => { Seq::empty() };
}
