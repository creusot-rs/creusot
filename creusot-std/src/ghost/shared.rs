use core::{marker::PhantomData, ops::Deref};
use creusot_std::prelude::*;

/// A type for sharing ghost data immutably.
#[builtin("identity")]
pub struct GhostShared<T>(PhantomData<*mut T>);

#[trusted]
unsafe impl<T: Sync> Send for GhostShared<T> {}

#[trusted]
unsafe impl<T: Sync> Sync for GhostShared<T> {}

impl<T> View for GhostShared<T> {
    type ViewTy = T;

    #[logic(open, inline)]
    fn view(self) -> T {
        self.val()
    }
}

impl<T> Invariant for GhostShared<T> {
    #[logic(open, prophetic)]
    fn invariant(self) -> bool {
        resolve(self.val()) && inv(self.val())
    }
}

impl<T> GhostShared<T> {
    /// Create a new shared ghost value.
    ///
    /// Note that the original value can never be retrieved, which allows this
    /// function to [`resolve`] it (in `GhostShared`'s type invariant).
    #[trusted]
    #[check(ghost)]
    #[ensures(result@ == *val)]
    #[allow(unused_variables)]
    pub fn new(val: Ghost<T>) -> Ghost<Self> {
        Ghost::conjure()
    }
}

impl<T> GhostShared<T> {
    /// The logical value contained in this `GhostShared`.
    #[logic]
    #[builtin("identity")]
    pub fn val(self) -> T {
        dead
    }

    /// Access the value of the `GhostShared` immutably.
    ///
    /// # Note on lifetimes
    ///
    /// Note that this function returns a borrow at an arbitrary lifetime
    /// `'a`. This is possible because `GhostShared` is a ghost-only type: the
    /// underlying `T` object is 'magically' made to live at least as long as
    /// `'a`.
    #[trusted]
    #[check(ghost)]
    #[ensures(*result == self.val())]
    pub fn to_ref<'a>(self) -> &'a T {
        unreachable!("ghost only")
    }
}

impl<T> AsRef<T> for GhostShared<T> {
    #[check(ghost)]
    #[ensures(*result == self.val())]
    fn as_ref(&self) -> &T {
        self.to_ref()
    }
}

impl<T> Clone for GhostShared<T> {
    #[check(ghost)]
    #[ensures(result == *self)]
    fn clone(&self) -> Self {
        *self
    }
}
impl<T> Copy for GhostShared<T> {}

impl<T> Deref for GhostShared<T> {
    type Target = T;

    #[check(ghost)]
    #[ensures(*result == self.val())]
    fn deref(&self) -> &T {
        self.to_ref()
    }
}
