use crate::{logic::Mapping, prelude::*};
use core::ops::Deref;

/// A borrow _guarded_ by an invariant.
///
/// This is used to define [`GuardedBorrow`].
/// This can also be used to define the equivalent of `GuardedBorrow` with
/// smart pointers, like [`RefMut`](core::cell::RefMut).
#[repr(transparent)]
#[logically_visible]
pub struct Guarded<T> {
    /// Borrow contained in this guard.
    ///
    /// The `T` type parameter is meant to be a mutable borrow type (like
    /// `&mut T`, or [`RefMut<T>`](core::cell::RefMut)).
    pub borrow: T,
    _guard: Snapshot<Mapping<T, bool>>,
}

impl<T> Guarded<T> {
    /// The [`guard`](Guard::guard) associated with this borrow.
    ///
    /// The type invariant of the `Guarded` ensures that the current value
    /// of [`borrow`](Self::borrow) satisfies this guard.
    #[logic(open, inline)]
    pub fn guard(self) -> Mapping<T, bool> {
        *self._guard
    }
}

impl<'a, T: ?Sized> Invariant for GuardedBorrow<'a, T> {
    #[logic(open, prophetic)]
    fn invariant(self) -> bool {
        pearlite! { self.guard()[self.borrow] }
    }
}

impl<T> Deref for Guarded<T> {
    type Target = T;
    #[ensures(*result == self.borrow)]
    #[check(ghost)]
    fn deref(&self) -> &Self::Target {
        &self.borrow
    }
}

// Forbid destructuring of `Guarded`
impl<T> Drop for Guarded<T> {
    fn drop(&mut self) {}
}

/// A mutable borrow, that asserts an invariant called the **guard**.
///
/// The guard can be broken locally, by accessing the [`borrow`](Self::borrow)
/// directly. However, it must be restored by the end of the `GuardedBorrow`'s
/// lifetime.
///
/// # Example
///
/// ```
/// use creusot_std::prelude::*;
/// use creusot_std::invariant::GuardedBorrow;
///
/// #[ensures(^b == 0i32)]
/// fn breaks_inv(b: &mut i32) { *b = 0; }
///
/// let mut x = 1;
/// let guarded = GuardedBorrow::new(&mut x, snapshot!(|x: i32| x == 1i32));
/// // break the guard...
/// breaks_inv(&mut *guarded.borrow);
/// // but restore it before we are done
/// *guarded.borrow = 1;
/// ```
pub type GuardedBorrow<'a, T> = Guarded<&'a mut T>;

impl<'a, T: ?Sized> GuardedBorrow<'a, T> {
    /// Create a new guarded borrow.
    ///
    /// The borrow contained in the result is guaranteed to satisfy the
    /// [`guard`](Guard::guard) at the end of its lifetime.
    ///
    /// Note that the `borrow` field cannot have its final value changed,
    /// ensuring that it will not get swapped for another borrow.
    #[trusted]
    #[ensures(result.borrow == borrow)]
    #[ensures(forall<bor: &mut T> result.guard()[bor] == (guard[*bor] && ^bor == ^borrow))]
    #[ensures(guard[^borrow])]
    #[check(ghost)]
    pub fn new(borrow: &'a mut T, #[allow(unused)] guard: Snapshot<Mapping<T, bool>>) -> Self {
        Self { borrow, _guard: snapshot!(|_: &mut T| false /* placeholder */) }
    }

    /// Get a shared borrow out of this guarded borrow.
    ///
    /// It is not possible to break the guard anymore, since the returned borrow
    /// is immutable.
    #[trusted]
    #[ensures(*result == *self.borrow)]
    #[ensures(*self.borrow == ^self.borrow)]
    #[check(ghost)]
    pub fn into_shared(self) -> &'a T {
        let ptr = self.borrow as *mut T;
        core::mem::forget(self);
        // SAFETY: we are bypassing the destructor of `self`, but it is ok since
        // it does nothing anyways.
        unsafe { &*ptr }
    }
}
