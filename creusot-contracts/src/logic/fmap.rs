use crate::{logic::Mapping, util::*, *};

#[cfg_attr(not(creusot), allow(dead_code))]
type PMap<K, V> = Mapping<K, Option<SizedW<V>>>;

/// A Map type usable in pearlite and `ghost!` blocks.
///
/// # Ghost
///
/// Since [`std::collections::HashMap`] and [`std::collections::BTreeMap`] have finite
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
#[trusted] //opaque
pub struct FMap<K, V: ?Sized>(std::marker::PhantomData<K>, std::marker::PhantomData<V>);

/// Logical definitions
impl<K, V: ?Sized> FMap<K, V> {
    #[trusted]
    #[logic]
    #[ensures(result >= 0)]
    pub fn len(self) -> Int {
        dead
    }

    #[trusted]
    #[logic]
    pub fn mk(_m: PMap<K, V>) -> Self {
        dead
    }

    #[trusted]
    #[logic]
    #[ensures(Self::mk(result) == self)] // injectivity
    pub fn view(self) -> PMap<K, V> {
        dead
    }

    #[trusted]
    #[logic]
    #[ensures(result.view() == self.view().set(k, Some(v.make_sized())))]
    #[ensures(self.contains(k) ==> result.len() == self.len())]
    #[ensures(!self.contains(k) ==> result.len() == self.len() + 1)]
    pub fn insert(self, k: K, v: V) -> Self {
        dead
    }

    #[trusted]
    #[logic]
    #[ensures(result.view() == self.view().set(k, None))]
    #[ensures(result.len() == if self.contains(k) {self.len() - 1} else {self.len()})]
    pub fn remove(self, k: K) -> Self {
        dead
    }

    #[logic]
    #[open]
    #[why3::attr = "inline:trivial"]
    pub fn get(self, k: K) -> Option<V>
    where
        V: Sized,
    {
        match self.get_unsized(k) {
            None => None,
            Some(x) => Some(*x),
        }
    }

    #[logic]
    #[open]
    #[why3::attr = "inline:trivial"]
    pub fn get_unsized(self, k: K) -> Option<SizedW<V>> {
        self.view().get(k)
    }

    #[logic]
    #[open]
    #[why3::attr = "inline:trivial"]
    pub fn lookup_unsized(self, k: K) -> SizedW<V> {
        unwrap(self.get_unsized(k))
    }

    #[logic]
    #[open]
    #[why3::attr = "inline:trivial"]
    pub fn lookup(self, k: K) -> V
    where
        V: Sized,
    {
        *self.lookup_unsized(k)
    }

    #[logic]
    #[open]
    #[why3::attr = "inline:trivial"]
    pub fn contains(self, k: K) -> bool {
        self.get_unsized(k) != None
    }

    #[trusted]
    #[logic]
    #[ensures(result.len() == 0)]
    #[ensures(result.view() == Mapping::cst(None))]
    pub fn empty() -> Self {
        dead
    }

    #[logic]
    #[open]
    pub fn is_empty(self) -> bool {
        self.ext_eq(FMap::empty())
    }

    #[logic]
    #[open]
    pub fn disjoint(self, other: Self) -> bool {
        pearlite! {forall<k: K> !self.contains(k) || !other.contains(k)}
    }

    #[logic]
    #[open]
    pub fn subset(self, other: Self) -> bool {
        pearlite! {
            forall<k: K> self.contains(k) ==> other.get_unsized(k) == self.get_unsized(k)
        }
    }

    #[trusted]
    #[logic]
    #[requires(self.disjoint(other))]
    #[ensures(forall<k: K> result.get_unsized(k) == if self.contains(k) {
        self.get_unsized(k)
    } else if other.contains(k) {
        other.get_unsized(k)
    } else {
        None
    })]
    #[ensures(result.len() == self.len() + other.len())]
    pub fn union(self, other: Self) -> Self {
        dead
    }

    #[trusted]
    #[logic]
    #[ensures(forall<k: K> result.get_unsized(k) == if other.contains(k) {
        None
    } else {
        self.get_unsized(k)
    })]
    pub fn subtract_keys(self, other: Self) -> Self {
        dead
    }

    #[logic]
    #[open]
    #[requires(other.subset(self))]
    #[ensures(result.disjoint(other))]
    #[ensures(other.union(result).ext_eq(self))]
    #[ensures(forall<k: K> result.get_unsized(k) == if other.contains(k) {
        None
    } else {
        self.get_unsized(k)
    })]
    pub fn subtract(self, other: Self) -> Self {
        self.subtract_keys(other)
    }

    #[logic]
    #[open]
    #[ensures(result ==> self == other)]
    #[ensures((forall<k: K> self.get_unsized(k) == other.get_unsized(k)) ==> result)]
    pub fn ext_eq(self, other: Self) -> bool {
        self.view() == other.view()
    }
}

impl<K, V> IndexLogic<K> for FMap<K, V> {
    type Item = V;

    #[logic]
    #[open]
    #[why3::attr = "inline:trivial"]
    fn index_logic(self, key: K) -> Self::Item {
        self.lookup(key)
    }
}

/// Ghost definitions
impl<K, V: ?Sized> FMap<K, V> {
    /// Create a new, empty map on the ghost heap.
    #[trusted]
    #[pure]
    #[ensures(result.is_empty())]
    #[allow(unreachable_code)]
    pub fn new() -> GhostBox<Self> {
        ghost!(panic!())
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
    #[pure]
    #[ensures(result == self.len())]
    pub fn len_ghost(&self) -> Int {
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
    #[pure]
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
    #[pure]
    #[ensures(if self.contains(*key) {
            match result {
                None => false,
                Some(r) => *self.lookup_unsized(*key) == *r,
            }
        } else {
            result == None
        })]
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
    ///     proof_assert!(map.lookup(1i32) == 42i32);
    /// };
    /// ```
    #[trusted]
    #[pure]
    #[ensures(if self.contains(*key) {
            match result {
                None => false,
                Some(r) => (^self).contains(*key) &&
                           *(*self).lookup_unsized(*key) == *r &&
                           *(^self).lookup_unsized(*key) == ^r,
            }
        } else {
            result == None && *self == ^self
        })]
    #[ensures(forall<k: K> k != *key ==> (*self).get_unsized(k) == (^self).get_unsized(k))]
    #[ensures((*self).len() == (^self).len())]
    pub fn get_mut_ghost(&mut self, key: &K) -> Option<&mut V> {
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
    ///     proof_assert!(map.lookup(37i32) == 42i32);
    /// };
    /// ```
    #[trusted]
    #[pure]
    #[ensures(^self == (*self).insert(key, value))]
    #[ensures(result == (*self).get(key))]
    pub fn insert_ghost(&mut self, key: K, value: V) -> Option<V>
    where
        V: Sized,
    {
        let _ = key;
        let _ = value;
        panic!()
    }

    /// Same as [`Self::insert_ghost`], but for unsized values.
    #[trusted]
    #[pure]
    #[ensures(^self == (*self).insert(key, *value))]
    #[ensures(result == (*self).get_unsized(key))]
    pub fn insert_ghost_unsized(&mut self, key: K, value: Box<V>) -> Option<Box<V>> {
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
    #[pure]
    #[ensures(^self == (*self).remove(*key))]
    #[ensures(result == (*self).get(*key))]
    pub fn remove_ghost(&mut self, key: &K) -> Option<V>
    where
        V: Sized,
    {
        let _ = key;
        panic!()
    }

    /// Same as [`Self::remove_ghost`], but for unsized values.
    #[trusted]
    #[pure]
    #[ensures(^self == (*self).remove(*key))]
    #[ensures(result == (*self).get_unsized(*key))]
    pub fn remove_ghost_unsized(&mut self, key: &K) -> Option<Box<V>> {
        let _ = key;
        panic!()
    }
}
