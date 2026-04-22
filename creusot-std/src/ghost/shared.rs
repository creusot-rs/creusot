use core::marker::PhantomData;
use creusot_std::prelude::*;

#[cfg(all(creusot, not(feature = "std")))]
use alloc::boxed::Box;

/// A type for sharing ghost data immutably.
#[opaque]
pub struct GhostShared<T: ?Sized>(PhantomData<fn() -> T>);

impl<T> View for GhostShared<T> {
    type ViewTy = T;

    #[logic(open)]
    fn view(self) -> T {
        *self.val()
    }
}

impl<T: ?Sized> Invariant for GhostShared<T> {
    #[logic(open, prophetic)]
    fn invariant(self) -> bool {
        resolve(self.val())
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

impl<T: ?Sized> GhostShared<T> {
    /// The logical value contained in this `GhostShared`.
    #[logic(opaque)]
    pub fn val(self) -> Box<T> {
        dead
    }

    #[logic(opaque)]
    #[trusted]
    #[requires(self.val() == other.val())]
    #[ensures(self == other)]
    pub fn ext_eq(self, other: Self) {}
}

impl<T: ?Sized> AsRef<T> for GhostShared<T> {
    /// Access the value of the `GhostShared` immutably.
    #[trusted]
    #[check(ghost)]
    #[ensures(*result == *self.val())]
    fn as_ref(&self) -> &T {
        unreachable!("ghost code only")
    }
}

impl<T: ?Sized> Clone for GhostShared<T> {
    #[check(ghost)]
    #[ensures(result == *self)]
    fn clone(&self) -> Self {
        *self
    }
}
impl<T: ?Sized> Copy for GhostShared<T> {}

impl<T: ?Sized> core::ops::Deref for GhostShared<T> {
    type Target = T;

    #[check(ghost)]
    #[ensures(*result == *self.val())]
    fn deref(&self) -> &T {
        self.as_ref()
    }
}
