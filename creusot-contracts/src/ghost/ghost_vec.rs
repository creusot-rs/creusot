use crate::{logic::Seq, *};

/// A [`Vec`] type usable in `ghost!` blocks.
///
/// Since [`Vec`] have finite capacity, this could cause some issues in ghost code:
/// ```rust,creusot,compile_fail
/// ghost! {
///     let mut v = Vec::new();
///     for _ in 0..=usize::MAX as u128 + 1 {
///         v.push(0); // cannot fail, since we are in a ghost block
///     }
///     proof_assert!(v.len() <= usize::MAX); // by definition
///     proof_assert!(v.len() > usize::MAX); // uh-oh
/// }
/// ```
///
/// This type is designed for this use-case, with no restriction on the capacity.
pub struct GhostVec<T>(Seq<T>);

impl<T> ShallowModel for GhostVec<T> {
    type ShallowModelTy = Seq<T>;

    #[logic]
    #[open(self)]
    fn shallow_model(self) -> Self::ShallowModelTy {
        self.0
    }
}

impl<T> GhostVec<T> {
    /// Constructs a new, empty `GhostVec<T>`.
    ///
    /// This is allocated on the ghost heap, and as such is wrapped in [`GhostBox`].
    #[trusted]
    #[pure]
    #[ensures(result@.len() == 0)]
    pub fn new() -> GhostBox<Self> {
        GhostBox::from_fn(|| loop {})
    }

    /// Returns the number of elements in the vector, also referred to as its 'length'.
    ///
    /// # Example
    /// ```rust,creusot
    /// use creusot_contracts::{ghost::GhostVec, *};
    ///
    /// let mut vec = GhostVec::new();
    /// ghost! {
    ///     vec.push(1);
    ///     vec.push(2);
    ///     vec.push(3);
    ///     let length = vec.len();
    ///     proof_assert!(length == 3);
    /// };
    /// ```
    #[trusted]
    #[pure]
    #[ensures(result == self@.len())]
    pub fn len(&self) -> Int {
        loop {}
    }

    /// Appends an element to the back of a collection.
    ///
    /// # Example
    /// ```rust,creusot
    /// use creusot_contracts::{ghost::GhostVec, *};
    ///
    /// let mut vec = GhostVec::new();
    /// ghost! {
    ///     vec.push(1);
    ///     vec.push(2);
    ///     vec.push(3);
    ///     proof_assert!(v@[0] == 1i32 && v@[1] == 2i32 && v@[2] == 3i32);
    /// };
    /// ```
    #[trusted]
    #[pure]
    #[ensures((^self)@ == (*self)@.push(x))]
    pub fn push(&mut self, x: T) {
        let _ = x;
        loop {}
    }

    /// Returns a reference to an element at `index` or `None` if `index` is out of bounds.
    ///
    /// # Example
    /// ```rust,creusot
    /// use creusot_contracts::{ghost::GhostVec, *};
    ///
    /// let mut v = GhostVec::new();
    /// ghost! {
    ///     v.push(10);
    ///     v.push(40);
    ///     v.push(30);
    ///     let get1 = v.get(*Int::new(1));
    ///     let get2 = v.get(*Int::new(3));
    ///     proof_assert!(get1 == Some(&40i32));
    ///     proof_assert!(get2 == None);
    /// };
    /// ```
    #[trusted]
    #[pure]
    #[ensures(match self@.get(index) {
        None => result == None,
        Some(v) => result == Some(&v),
    })]
    pub fn get(&self, index: Int) -> Option<&T> {
        let _ = index;
        loop {}
    }

    /// Returns a mutable reference to an element at `index` or `None` if `index` is out of bounds.
    ///
    /// # Example
    /// ```rust,creusot
    /// use creusot_contracts::{ghost::GhostVec, *};
    ///
    /// let mut v = GhostVec::new();
    ///
    /// ghost! {
    ///     v.push(0);
    ///     v.push(1);
    ///     v.push(2);
    ///     if let Some(elem) = v.get_mut(*Int::new(1)) {
    ///         *elem = 42;
    ///     }
    ///     proof_assert!(v@[0] == 0i32 && v@[1] == 42i32 && v@[2] == 2i32);
    /// };
    /// ```
    #[trusted]
    #[pure]
    #[ensures(if self@.get(index) == None {
        result == None && *self == ^self
    } else {
        match result {
            None => false,
            Some(r) => *r == (*self)@[index] && ^r == (^self)@[index]
        }
    })]
    #[ensures(forall<i: Int> i != index ==> (*self)@.get(index) == (^self)@.get(index))]
    #[ensures((*self)@.len() == (^self)@.len())]
    pub fn get_mut(&mut self, index: Int) -> Option<&mut T> {
        let _ = index;
        loop {}
    }

    /// Removes the last element from a vector and returns it, or `None` if it is empty.
    ///
    /// # Example
    /// ```rust,creusot
    /// use creusot_contracts::{ghost::GhostVec, *};
    ///
    /// let mut vec = GhostVec::new();
    /// ghost! {
    ///     vec.push(1);
    ///     vec.push(2);
    ///     vec.push(3);
    ///     let popped = vec.pop();
    ///     proof_assert!(popped == Some(3i32));
    ///     proof_assert!(vec@[0] == 1i32 && vec@[1] == 2i32);
    /// };
    /// ```
    #[trusted]
    #[pure]
    #[ensures(if self@.len() == 0 {
        (*self) == (^self) && result == None
    } else {
        match result {
            None => false,
            Some(r) => (*self)@ == (^self)@.push(r)
        }
    })]
    pub fn pop(&mut self) -> Option<T> {
        loop {}
    }
}
