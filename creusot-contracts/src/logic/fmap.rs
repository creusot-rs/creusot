#[cfg(creusot)]
use crate::resolve::structural_resolve;
use crate::{
    logic::{FSet, Mapping, ops::IndexLogic},
    std::option::OptionExt as _,
    *,
};

/// A finite map type usable in pearlite and `ghost!` blocks.
///
/// If you need an infinite map, see [`Mapping`].
///
/// # Ghost
///
/// Since [`std::collections::HashMap`](::std::collections::HashMap) and
/// [`std::collections::BTreeMap`](::std::collections::BTreeMap) have finite
/// capacity, this could cause some issues in ghost code:
/// ```rust,creusot,compile_fail
/// ghost! {
///     let mut map = HashMap::new();
///     for _ in 0..=usize::MAX as u128 + 1 {
///         map.insert(0, 0); // cannot fail, since we are in a ghost block
///     }
///     proof_assert!(map.len() <= usize::MAX@); // by definition
///     proof_assert!(map.len() > usize::MAX@); // uh-oh
/// }
/// ```
///
/// This type is designed for this use-case, with no restriction on the capacity.
#[opaque]
pub struct FMap<K: ?Sized, V>(std::marker::PhantomData<K>, std::marker::PhantomData<V>);

impl<K: ?Sized, V> View for FMap<K, V> {
    type ViewTy = Mapping<K, Option<V>>;

    /// View of the map
    ///
    /// This represents the actual content of the map: other methods are specified relative to this.
    #[logic(opaque)]
    // Adding this injectivity post-condition makes the SMT timeout on many examples
    //#[ensures(forall<m: Self> result == m@ ==> self == m)]
    //TODO: investigate
    fn view(self) -> Self::ViewTy {
        dead
    }
}

/// Logical definitions
impl<K: ?Sized, V> FMap<K, V> {
    /// Returns the empty map.
    #[trusted]
    #[logic(opaque)]
    #[ensures(result.len() == 0)]
    #[ensures(result@ == Mapping::cst(None))]
    pub fn empty() -> Self {
        dead
    }

    /// The number of elements in the map, also called its length.
    #[trusted]
    #[logic(opaque)]
    #[ensures(result >= 0)]
    pub fn len(self) -> Int {
        dead
    }

    /// Returns a new map, where the key-value pair `(k, v)` has been inserted.
    #[trusted]
    #[logic(opaque)]
    #[ensures(result@ == self@.set(k, Some(v)))]
    #[ensures(result.len() == if self.contains(k) { self.len() } else { self.len() + 1 })]
    pub fn insert(self, k: K, v: V) -> Self {
        dead
    }

    /// Returns the map where containing the only key-value pair `(k, v)`.
    #[logic(open)]
    pub fn singleton(k: K, v: V) -> Self {
        Self::empty().insert(k, v)
    }

    /// Returns a new map, where the key `k` is no longer present.
    #[trusted]
    #[logic(opaque)]
    #[ensures(result@ == self@.set(k, None))]
    #[ensures(result.len() == if self.contains(k) {self.len() - 1} else {self.len()})]
    pub fn remove(self, k: K) -> Self {
        dead
    }

    /// Get the value associated with key `k` in the map.
    ///
    /// If no value is present, returns [`None`].
    #[logic(open, inline)]
    pub fn get(self, k: K) -> Option<V> {
        self.view().get(k)
    }

    /// Get the value associated with key `k` in the map.
    ///
    /// If no value is present, the returned value is meaningless.
    #[logic(open, inline)]
    pub fn lookup(self, k: K) -> V {
        self.get(k).unwrap_logic()
    }

    /// Returns `true` if the map contains a value for the specified key.
    #[logic(open, inline)]
    pub fn contains(self, k: K) -> bool {
        self.get(k) != None
    }

    /// Returns `true` if the map contains no elements.
    #[logic(open)]
    pub fn is_empty(self) -> bool {
        self.ext_eq(FMap::empty())
    }

    /// Returns `true` if the two maps have no key in common.
    #[logic(open)]
    pub fn disjoint(self, other: Self) -> bool {
        pearlite! {forall<k: K> !self.contains(k) || !other.contains(k)}
    }

    /// Returns `true` if all key-value pairs in `self` are also in `other`.
    #[logic(open)]
    pub fn subset(self, other: Self) -> bool {
        pearlite! {
            forall<k: K> self.contains(k) ==> other.get(k) == self.get(k)
        }
    }

    /// Returns a new map, which is the union of `self` and `other`.
    ///
    /// If `self` and `other` are not [`disjoint`](Self::disjoint), the result is unspecified.
    #[trusted]
    #[logic(opaque)]
    #[requires(self.disjoint(other))]
    #[ensures(forall<k: K> #[trigger(result.get(k))] !self.contains(k) ==> result.get(k) == other.get(k))]
    #[ensures(forall<k: K> #[trigger(result.get(k))] !other.contains(k) ==> result.get(k) == self.get(k))]
    #[ensures(result.len() == self.len() + other.len())]
    pub fn union(self, other: Self) -> Self {
        dead
    }

    /// Returns a new map, that contains all the key-value pairs of `self` such that the
    /// key is not in `other`.
    #[trusted]
    #[logic(opaque)]
    #[ensures(result.disjoint(other))]
    #[ensures(other.subset(self) ==> other.union(result) == self)]
    #[ensures(forall<k: K> #[trigger(result.get(k))] result.get(k) ==
        if other.contains(k) {
            None
        } else {
            self.get(k)
        }
    )]
    pub fn subtract(self, other: Self) -> Self {
        dead
    }

    /// Injectivity of view. Private axiom used by ext_eq
    #[logic]
    #[trusted]
    #[requires(self@ == other@)]
    #[ensures(self == other)]
    fn view_inj(self, other: Self) {}

    /// Extensional equality.
    ///
    /// Returns `true` if `self` and `other` contain exactly the same key-value pairs.
    ///
    /// This is in fact equivalent with normal equality.
    #[logic(open)]
    #[ensures(result == (self == other))]
    pub fn ext_eq(self, other: Self) -> bool {
        pearlite! {
            let _ = Self::view_inj;
            forall<k: K> self.get(k) == other.get(k)
        }
    }

    /// Merge the two maps together
    ///
    /// If both map contain the same key, the entry for the result is determined by `f`.
    #[trusted]
    #[logic(opaque)]
    #[ensures(
        forall<k: K> #[trigger(result.get(k))]
            match (self.get(k), m.get(k)) {
                (None, y) => result.get(k) == y,
                (x, None) => result.get(k) == x,
                (Some(x), Some(y)) => result.get(k) == Some(f[(x, y)]),
            }
    )]
    pub fn merge(self, m: FMap<K, V>, f: Mapping<(V, V), V>) -> FMap<K, V> {
        dead
    }

    /// Map every value in `self` according to `f`. Keys are unchanged.
    #[logic]
    #[trusted] // The ensures clause that says the lenght do not change is rather difficult
    #[ensures(forall<k: K> #[trigger(result.get(k))] result.get(k) == match self.get(k) {
        None => None,
        Some(v) => Some(f[(k, v)]),
    })]
    #[ensures(result.len() == self.len())]
    pub fn map<V2>(self, f: Mapping<(K, V), V2>) -> FMap<K, V2>
    where
        K: Sized,
    {
        self.filter_map(|(k, v)| Some(f[(k, v)]))
    }

    /// Filter key-values in `self` according to `p`.
    ///
    /// A key-value pair will be in the result map if and only if it is in `self` and
    /// `p` returns `true` on this pair.
    #[logic]
    #[ensures(forall<k: K> #[trigger(result.get(k))] result.get(k) == match self.get(k) {
        None => None,
        Some(v) => if p[(k, v)] { Some(v) } else { None },
    })]
    pub fn filter(self, p: Mapping<(K, V), bool>) -> Self
    where
        K: Sized,
    {
        self.filter_map(|(k, v)| if p[(k, v)] { Some(v) } else { None })
    }

    /// Map every value in `self` according to `f`. Keys are unchanged.
    /// If `f` returns `false`, remove the key-value from the map.
    #[trusted]
    #[logic(opaque)]
    #[ensures(forall<k: K> #[trigger(result.get(k))] result.get(k) == match self.get(k) {
        None => None,
        Some(v) => f[(k, v)],
    })]
    pub fn filter_map<V2>(self, f: Mapping<(K, V), Option<V2>>) -> FMap<K, V2>
    where
        K: Sized,
    {
        dead
    }

    /// Returns the set of keys in the map.
    #[trusted]
    #[logic(opaque)]
    #[ensures(forall<k: K> result.contains(k) == self.contains(k))]
    #[ensures(result.len() == self.len())]
    pub fn keys(self) -> FSet<K> {
        dead
    }
}

impl<K: ?Sized, V> IndexLogic<K> for FMap<K, V> {
    type Item = V;

    #[logic(open, inline)]
    fn index_logic(self, key: K) -> Self::Item {
        self.lookup(key)
    }
}

/// Ghost definitions
impl<K, V> FMap<K, V> {
    /// Create a new, empty map on the ghost heap.
    #[trusted]
    #[check(ghost)]
    #[ensures(result.is_empty())]
    #[allow(unreachable_code)]
    pub fn new() -> Ghost<Self> {
        Ghost::conjure()
    }

    /// Returns the number of elements in the map.
    ///
    /// If you need to get the length in pearlite, consider using [`len`](Self::len).
    ///
    /// # Example
    /// ```rust,creusot
    /// use creusot_contracts::{logic::FMap, *};
    ///
    /// let mut map = FMap::new();
    /// ghost! {
    ///     let len1 = map.len_ghost();
    ///     map.insert_ghost(1, 21);
    ///     map.insert_ghost(1, 42);
    ///     map.insert_ghost(2, 50);
    ///     let len2 = map.len_ghost();
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

    #[trusted]
    #[check(ghost)]
    #[ensures(result == (self.len() == 0 && forall<k> !self.contains(k)))]
    pub fn is_empty_ghost(&self) -> bool {
        panic!()
    }

    /// Returns true if the map contains a value for the specified key.
    ///
    /// # Example
    /// ```rust,creusot
    /// use creusot_contracts::{logic::FMap, *};
    ///
    /// let mut map = FMap::new();
    /// ghost! {
    ///     map.insert_ghost(1, 42);
    ///     let (b1, b2) = (map.contains_ghost(&1), map.contains_ghost(&2));
    ///     proof_assert!(b1);
    ///     proof_assert!(!b2);
    /// };
    /// ```
    #[check(ghost)]
    #[ensures(result == self.contains(*key))]
    pub fn contains_ghost(&self, key: &K) -> bool {
        self.get_ghost(key).is_some()
    }

    /// Returns a reference to the value corresponding to the key.
    ///
    /// # Example
    /// ```rust,creusot
    /// use creusot_contracts::{logic::FMap, *};
    ///
    /// let mut map = FMap::new();
    /// ghost! {
    ///     map.insert_ghost(1, 2);
    ///     let x1 = map.get_ghost(&1);
    ///     let x2 = map.get_ghost(&2);
    ///     proof_assert!(x1 == Some(&2));
    ///     proof_assert!(x2 == None);
    /// };
    /// ```
    #[trusted]
    #[check(ghost)]
    #[ensures(result == self.get(*key).map_logic(|v|&v))]
    pub fn get_ghost(&self, key: &K) -> Option<&V> {
        let _ = key;
        panic!()
    }

    /// Returns a mutable reference to the value corresponding to the key.
    ///
    /// # Example
    /// ```rust,creusot
    /// use creusot_contracts::{logic::FMap, *};
    ///
    /// let mut map = FMap::new();
    /// ghost! {
    ///     map.insert_ghost(1, 21);
    ///     if let Some(x) = map.get_mut_ghost(&1) {
    ///         *x = 42;
    ///     }
    ///     proof_assert!(map[1i32] == 42i32);
    /// };
    /// ```
    #[trusted]
    #[check(ghost)]
    #[ensures(if self.contains(*key) {
            match result {
                None => false,
                Some(r) =>
                    (^self).contains(*key) && self[*key] == *r && (^self)[*key] == ^r,
            }
        } else {
            result == None && *self == ^self
        })]
    #[ensures(forall<k: K> k != *key ==> (*self).get(k) == (^self).get(k))]
    #[ensures((*self).len() == (^self).len())]
    pub fn get_mut_ghost(&mut self, key: &K) -> Option<&mut V> {
        let _ = key;
        panic!()
    }

    /// Returns a mutable reference to the value corresponding to a key, while still allowing
    /// modification on the other keys.
    ///
    /// # Example
    /// ```rust,creusot
    /// use creusot_contracts::{logic::FMap, *};
    ///
    /// let mut map = FMap::new();
    /// ghost! {
    ///     map.insert_ghost(1, 21);
    ///     map.insert_ghost(2, 42);
    ///     let (x, map2) = map.split_mut_ghost(&1);
    ///     *x = 22;
    ///     map2.insert_ghost(3, 30);
    ///     map2.insert_ghost(1, 56); // This modification will be ignored on `map`
    ///     proof_assert!(map[1i32] == 22i32);
    ///     proof_assert!(map[2i32] == 42i32);
    ///     proof_assert!(map[3i32] == 30i32);
    /// };
    /// ```
    #[trusted]
    #[check(ghost)]
    #[requires(self.contains(*key))]
    #[ensures(*result.1 == (*self).remove(*key))]
    #[ensures(self[*key] == *result.0 && ^self == (^result.1).insert(*key, ^result.0))]
    pub fn split_mut_ghost(&mut self, key: &K) -> (&mut V, &mut Self) {
        let _ = key;
        panic!()
    }

    /// Inserts a key-value pair into the map.
    ///
    /// If the map did not have this key present, `None` is returned.
    ///
    /// # Example
    /// ```rust,creusot
    /// use creusot_contracts::{logic::FMap, *};
    ///
    /// let mut map = FMap::new();
    /// ghost! {
    ///     let res1 = map.insert_ghost(37, 41);
    ///     proof_assert!(res1 == None);
    ///     proof_assert!(map.is_empty() == false);
    ///
    ///     let res2 = map.insert_ghost(37, 42);
    ///     proof_assert!(res2 == Some(41));
    ///     proof_assert!(map[37i32] == 42i32);
    /// };
    /// ```
    #[trusted]
    #[check(ghost)]
    #[ensures(^self == (*self).insert(key, value))]
    #[ensures(result == (*self).get(key))]
    pub fn insert_ghost(&mut self, key: K, value: V) -> Option<V> {
        let _ = key;
        let _ = value;
        panic!()
    }

    /// Removes a key from the map, returning the value at the key if the key was previously in the map.
    ///
    /// # Example
    /// ```rust,creusot
    /// use creusot_contracts::{logic::FMap, *};
    ///
    /// let mut map = FMap::new();
    /// let res = ghost! {
    ///     map.insert_ghost(1, 42);
    ///     let res1 = map.remove_ghost(&1);
    ///     let res2 = map.remove_ghost(&1);
    ///     proof_assert!(res1 == Some(42i32));
    ///     proof_assert!(res2 == None);
    /// };
    /// ```
    #[trusted]
    #[check(ghost)]
    #[ensures(^self == (*self).remove(*key))]
    #[ensures(result == (*self).get(*key))]
    pub fn remove_ghost(&mut self, key: &K) -> Option<V> {
        let _ = key;
        panic!()
    }

    /// Clears the map, removing all values.
    ///
    /// # Example
    /// ```rust,creusot
    /// use creusot_contracts::{ghost, proof_assert, logic::FMap};
    ///
    /// let mut s = FMap::new();
    /// ghost! {
    ///     s.insert_ghost(1, 2);
    ///     s.insert_ghost(2, 3);
    ///     s.insert_ghost(3, 42);
    ///     s.clear_ghost();
    ///     proof_assert!(s == FMap::empty());
    /// };
    /// ```
    #[trusted]
    #[check(ghost)]
    #[ensures(^self == Self::empty())]
    pub fn clear_ghost(&mut self) {}

    #[trusted]
    #[check(ghost)]
    #[ensures(match result {
        None => *self == ^self && self.is_empty(),
        Some((k, v)) => *self == (^self).insert(k, v) && !(^self).contains(k),
    })]
    pub fn remove_one_ghost(&mut self) -> Option<(K, V)> {
        panic!()
    }

    #[trusted]
    #[check(ghost)]
    #[ensures(result.len() == self.len())]
    #[ensures(forall<k, v> (self.get(k) == Some(v)) == (exists<i> result.get(i) == Some((k, v))))]
    pub fn to_seq(self) -> Seq<(K, V)> {
        panic!()
    }

    #[trusted]
    #[check(ghost)]
    #[ensures(result.len() == self.len())]
    #[ensures(forall<k, v> (self.get(k) == Some(v)) == (result.get(&k) == Some(&v)))]
    pub fn as_ref_ghost(&self) -> FMap<&K, &V> {
        panic!()
    }

    #[trusted]
    #[check(ghost)]
    #[ensures(result.len() == self.len())]
    #[ensures(forall<k> match result.get(&k) {
        None => !(*self).contains(k) && !(^self).contains(k),
        Some(v) => (*self).get(k) == Some(*v) && (^self).get(k) == Some(^v),
    })]
    pub fn as_mut_ghost(&mut self) -> FMap<&K, &mut V> {
        panic!()
    }
}

impl<'a, K, V> ::std::ops::Index<&'a K> for FMap<K, V> {
    type Output = V;

    #[check(ghost)]
    #[requires(self.contains(*key))]
    #[ensures(Some(*result) == self.get(*key))]
    fn index(&self, key: &'a K) -> &Self::Output {
        self.get_ghost(key).unwrap()
    }
}

impl<K: Clone + Copy, V: Clone + Copy> Clone for FMap<K, V> {
    #[trusted]
    #[check(ghost)]
    #[ensures(result == *self)]
    fn clone(&self) -> Self {
        *self
    }
}

// Having `Copy` guarantees that the operation is pure, even if we decide to change the definition of `Clone`.
impl<K: Clone + Copy, V: Clone + Copy> Copy for FMap<K, V> {}

impl<K: ?Sized, V> Invariant for FMap<K, V> {
    #[logic(open, prophetic, inline)]
    #[creusot::trusted_is_tyinv_trivial_if_param_trivial]
    fn invariant(self) -> bool {
        pearlite! { forall<k: K> self.contains(k) ==> inv(k) && inv(self[k]) }
    }
}

// =========
// Iterators
// =========

impl<K, V> IntoIterator for FMap<K, V> {
    type Item = (K, V);
    type IntoIter = FMapIter<K, V>;

    #[check(ghost)]
    #[ensures(result@ == self)]
    fn into_iter(self) -> Self::IntoIter {
        FMapIter { inner: self }
    }
}

/// An owning iterator for [`FMap`].
pub struct FMapIter<K, V> {
    inner: FMap<K, V>,
}

impl<K, V> View for FMapIter<K, V> {
    type ViewTy = FMap<K, V>;
    #[logic]
    fn view(self) -> Self::ViewTy {
        self.inner
    }
}

impl<K, V> ::std::iter::Iterator for FMapIter<K, V> {
    type Item = (K, V);

    #[check(ghost)]
    #[ensures(match result {
        None => self.completed(),
        Some((k, v)) => (*self).produces(Seq::singleton((k, v)), ^self) && (*self)@ == (^self)@.insert(k, v),
    })]
    fn next(&mut self) -> Option<(K, V)> {
        self.inner.remove_one_ghost()
    }
}

impl<K, V> crate::Iterator for FMapIter<K, V> {
    #[logic(prophetic, open)]
    fn produces(self, visited: Seq<(K, V)>, o: Self) -> bool {
        pearlite! {
            // We cannot visit the same key twice
            (forall<i, j> 0 <= i && i < j && j < visited.len() ==> visited[i].0 != visited[j].0) &&
            // If a key-value is visited, it was in `self` but not in `o`
            (forall<k, v, i> visited.get(i) == Some((k, v)) ==> !o@.contains(k) && self@.get(k) == Some(v)) &&
            // Helper for the length
            self@.len() == visited.len() + o@.len() &&
            // else, the key-value is the same in `self` and `o`
            (forall<k> (forall<i> 0 <= i && i < visited.len() ==> visited[i].0 != k) ==> o@.get(k) == self@.get(k))
        }
    }

    #[logic(prophetic, open)]
    fn completed(&mut self) -> bool {
        pearlite! { self@.is_empty() }
    }

    #[logic(law)]
    #[ensures(self.produces(Seq::empty(), self))]
    fn produces_refl(self) {}

    #[logic(law)]
    #[requires(a.produces(ab, b))]
    #[requires(b.produces(bc, c))]
    #[ensures(a.produces(ab.concat(bc), c))]
    fn produces_trans(a: Self, ab: Seq<Self::Item>, b: Self, bc: Seq<Self::Item>, c: Self) {
        let ac = ab.concat(bc);
        proof_assert!(forall<x> ab.contains(x) ==> ac.contains(x));
        proof_assert!(forall<i> 0 <= i && i < bc.len() ==> ac[i + ab.len()] == bc[i]);
        proof_assert!(forall<k> (forall<i> 0 <= i && i < ac.len() ==> ac[i].0 != k) ==> {
            (forall<i> 0 <= i && i < ab.len() ==> ab[i].0 != k) &&
            (forall<i> 0 <= i && i < bc.len() ==> bc[i].0 != k) &&
            a@.get(k) == b@.get(k) && b@.get(k) == c@.get(k)
        });
    }
}

impl<'a, K, V> IntoIterator for &'a FMap<K, V> {
    type Item = (&'a K, &'a V);
    type IntoIter = FMapIterRef<'a, K, V>;

    #[check(ghost)]
    #[ensures(result@ == *self)]
    fn into_iter(self) -> FMapIterRef<'a, K, V> {
        let _self = snapshot!(self);
        let result = FMapIterRef { inner: self.as_ref_ghost() };
        proof_assert!(result@.ext_eq(**_self));
        result
    }
}

/// An iterator over references in a [`FMap`].
pub struct FMapIterRef<'a, K, V> {
    inner: FMap<&'a K, &'a V>,
}

impl<K, V> View for FMapIterRef<'_, K, V> {
    type ViewTy = FMap<K, V>;
    #[logic]
    fn view(self) -> FMap<K, V> {
        pearlite! { logic::such_that(|m: FMap<K, V>|
            forall<k, v> (m.get(k) == Some(v)) == (self.inner.get(&k) == Some(&v))
        ) }
    }
}

impl<'a, K, V> ::std::iter::Iterator for FMapIterRef<'a, K, V> {
    type Item = (&'a K, &'a V);

    #[trusted] // FIXME: the definition of the view makes this incredibly hard to prove.
    #[check(ghost)]
    #[ensures(match result {
        None => self.completed(),
        Some(v) => (*self).produces(Seq::singleton(v), ^self)
    })]
    fn next(&mut self) -> Option<(&'a K, &'a V)> {
        self.inner.remove_one_ghost()
    }
}

impl<'a, K, V> crate::Iterator for FMapIterRef<'a, K, V> {
    #[logic(prophetic, open)]
    fn produces(self, visited: Seq<(&'a K, &'a V)>, o: Self) -> bool {
        pearlite! {
            // We cannot visit the same key twice
            (forall<i, j> 0 <= i && i < j && j < visited.len() ==> visited[i].0 != visited[j].0) &&
            // If a key-value is visited, it was in `self` but not in `o`
            (forall<k, v, i> visited.get(i) == Some((&k, &v)) ==> !o@.contains(k) && self@.get(k) == Some(v)) &&
            // else, the key-value is the same in `self` and `o`
            (forall<k> (forall<i> 0 <= i && i < visited.len() ==> visited[i].0 != &k) ==> o@.get(k) == self@.get(k))
        }
    }

    #[logic(prophetic, open)]
    fn completed(&mut self) -> bool {
        pearlite! { self@.is_empty() }
    }

    #[logic(law)]
    #[ensures(self.produces(Seq::empty(), self))]
    fn produces_refl(self) {}

    #[logic(law)]
    #[requires(a.produces(ab, b))]
    #[requires(b.produces(bc, c))]
    #[ensures(a.produces(ab.concat(bc), c))]
    fn produces_trans(a: Self, ab: Seq<Self::Item>, b: Self, bc: Seq<Self::Item>, c: Self) {
        let ac = ab.concat(bc);
        proof_assert!(forall<x> ab.contains(x) ==> ac.contains(x));
        proof_assert!(forall<i> 0 <= i && i < bc.len() ==> ac[i + ab.len()] == bc[i]);
        proof_assert!(forall<k> (forall<i> 0 <= i && i < ac.len() ==> ac[i].0 != k) ==> {
            (forall<i> 0 <= i && i < ab.len() ==> ab[i].0 != k) &&
            (forall<i> 0 <= i && i < bc.len() ==> bc[i].0 != k) &&
            a@.get(*k) == b@.get(*k) && b@.get(*k) == c@.get(*k)
        });
    }
}

impl<K: ?Sized, V> Resolve for FMap<K, V> {
    #[logic(open, prophetic)]
    fn resolve(self) -> bool {
        pearlite! { forall<k: K, v: V> self.get(k) == Some(v) ==> resolve(k) && resolve(v) }
    }

    #[trusted]
    #[logic(open(self), prophetic)]
    #[requires(structural_resolve(self))]
    #[ensures(self.resolve())]
    fn resolve_coherence(self) {}
}

impl<K, V> Resolve for FMapIter<K, V> {
    #[logic(open, prophetic)]
    fn resolve(self) -> bool {
        pearlite! { resolve(self@) }
    }

    #[trusted]
    #[logic(open(self), prophetic)]
    #[requires(structural_resolve(self))]
    #[ensures(self.resolve())]
    fn resolve_coherence(self) {}
}
