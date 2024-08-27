use crate::{logic::FMap, *};

/// A Map type usable in `ghost!` blocks.
///
/// Since [`std::collections::HashMap`] and [`std::collections::BTreeMap`] have finite
/// capacity, this could cause some issues in ghost code:
/// ```rust,creusot,compile_fail
/// ghost! {
///     let mut map = HashMap::new();
///     for _ in 0..=usize::MAX as u128 + 1 {
///         map.insert(0, 0); // cannot fail, since we are in a ghost block
///     }
///     proof_assert!(map.len() <= usize::MAX); // by definition
///     proof_assert!(map.len() > usize::MAX); // uh-oh
/// }
/// ```
///
/// This type is designed for this use-case, with no restriction on the capacity.
pub struct GhostMap<K, V>(FMap<K, V>);

impl<K, V> ShallowModel for GhostMap<K, V> {
    type ShallowModelTy = FMap<K, V>;

    #[logic]
    #[open(self)]
    fn shallow_model(self) -> Self::ShallowModelTy {
        self.0
    }
}

impl<K, V> GhostMap<K, V> {
    #[predicate(prophetic)]
    #[open]
    pub fn unmodified_key(&mut self, key: K) -> bool {
        pearlite! { (*self)@.get(key) == (^self)@.get(key) }
    }

    #[trusted]
    #[pure]
    #[ensures(result@.is_empty())]
    /// Create a new, empty map on the ghost heap.
    pub fn new() -> GhostBox<Self> {
        GhostBox::from_fn(|| loop {})
    }

    /// Returns the number of elements in the map.
    ///
    /// # Example
    /// ```rust,creusot
    /// use creusot_contracts::{ghost::GhostMap, *};
    ///
    /// let mut map = GhostMap::new();
    /// let lengths = ghost! {
    ///     let len1 = map.len();
    ///     map.insert(1, 21);
    ///     map.insert(1, 42);
    ///     map.insert(2, 50);
    ///     let len2 = map.len();
    ///     (len1, len2)
    /// };
    /// proof_assert!(length.inner().0 == 0);
    /// proof_assert!(length.inner().1 == 2);
    /// ```
    #[trusted]
    #[pure]
    #[ensures(result == self@.len())]
    pub fn len(&self) -> Int {
        loop {}
    }

    /// Returns true if the map contains a value for the specified key.
    ///
    /// # Example
    /// ```rust,creusot
    /// use creusot_contracts::{ghost::GhostMap, *};
    ///
    /// let mut map = GhostMap::new();
    /// let contains = ghost! {
    ///     map.insert(1, 42);
    ///     (map.contains(&1), map.contains(&2))
    /// };
    /// proof_assert!(contains.inner().0);
    /// proof_assert!(!contains.inner().1);
    /// ```
    #[pure]
    #[ensures(self@.contains(*key))]
    pub fn contains(&self, key: &K) -> bool {
        self.get(key).is_some()
    }

    /// Returns a reference to the value corresponding to the key.
    ///
    /// # Example
    /// ```rust,creusot
    /// use creusot_contracts::{ghost::GhostMap, *};
    ///
    /// let mut map = GhostMap::new();
    /// ghost! {
    ///     map.insert(1, 2);
    ///     proof_assert!(map.get(&1) == Some(&2));
    ///     proof_assert!(map.get(&2) == None);
    /// };
    /// ```
    #[trusted]
    #[pure]
    #[ensures(if self@.contains(*key) {
        result == Some(&self@.lookup(*key))
    } else {
        result == None
    })]
    pub fn get(&self, key: &K) -> Option<&V> {
        let _ = key;
        loop {}
    }

    /// Returns a mutable reference to the value corresponding to the key.
    ///
    /// # Example
    /// ```rust,creusot
    /// use creusot_contracts::{ghost::GhostMap, *};
    ///
    /// let mut map = GhostMap::new();
    /// ghost! {
    ///     map.insert(1, 21);
    ///     if let Some(x) = map.get_mut(&1) {
    ///         *x = 42;
    ///     }
    /// };
    /// proof_assert!(map@.lookup(1i32) == 42i32);
    /// ```
    #[trusted]
    #[pure]
    #[ensures(if self@.contains(*key) {
        match result {
            None => false,
            Some(r) => self@.lookup(*key) == *r && (^self)@.lookup(*key) == ^r,
        }
    } else {
        result == None
    })]
    #[ensures(forall<k: K> k != *key ==> self.unmodified_key(k))]
    #[ensures((*self)@.len() == (^self)@.len())]
    pub fn get_mut(&mut self, key: &K) -> Option<&mut V> {
        let _ = key;
        loop {}
    }

    /// Inserts a key-value pair into the map.
    ///
    /// If the map did not have this key present, `None` is returned.
    ///
    /// # Example
    /// ```rust,creusot
    /// use creusot_contracts::{ghost::GhostMap, *};
    ///
    /// let mut map = GhostMap::new();
    /// ghost! {
    ///     proof_assert!(map.insert(37, 41) == None);
    ///     proof_assert!(map.is_empty() == false);
    ///
    ///     map.insert(37, 42);
    ///     proof_assert!(map.insert(37, 43) == Some(42));
    ///     proof_assert!(map.get(&37) == Some(&43));
    /// };
    /// ```
    #[trusted]
    #[pure]
    #[ensures((^self)@ == (*self)@.insert(key, value))]
    #[ensures(if self@.contains(key) {
        result == Some((*self)@.lookup(key))
    } else {
        result == None
    })]
    pub fn insert(&mut self, key: K, value: V) -> Option<V> {
        let _ = key;
        let _ = value;
        loop {}
    }

    /// Removes a key from the map, returning the value at the key if the key was previously in the map.
    ///
    /// # Example
    /// ```rust,creusot
    /// use creusot_contracts::{ghost::GhostMap, *};
    ///
    /// let mut map = GhostMap::new();
    /// ghost! {
    ///     map.insert(1, 42);
    ///     proof_assert!(map.remove(&1) == Some(42));
    ///     proof_assert!(map.remove(&1) == None);
    /// };
    /// ```
    #[trusted]
    #[pure]
    #[ensures((^self)@ == (*self)@.remove(*key))]
    #[ensures(match self@.get(*key) {
        None => result == None,
        Some(v) => result == Some(*v),
    })]
    pub fn remove(&mut self, key: &K) -> Option<V> {
        let _ = key;
        loop {}
    }
}
