use crate::{logic::Mapping, prelude::*};
use core::ops::Deref;

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
#[repr(transparent)]
#[logically_visible]
pub struct GuardedBorrow<'a, T: ?Sized> {
    pub borrow: &'a mut T,
    _guard: Snapshot<Mapping<T, bool>>,
    _initial: Snapshot<&'a mut T>,
}

impl<'a, T: ?Sized> Invariant for GuardedBorrow<'a, T> {
    #[logic(open, prophetic)]
    fn invariant(self) -> bool {
        pearlite! { self.guard()[*self.borrow] && *self.prophecy() == ^self.borrow }
    }
}

// Forbid destructuring of `GuardedBorrow`
impl<'a, T: ?Sized> Drop for GuardedBorrow<'a, T> {
    fn drop(&mut self) {}
}

impl<'a, T: ?Sized> Deref for GuardedBorrow<'a, T> {
    type Target = T;
    #[ensures(*result == *self.borrow)]
    #[check(ghost)]
    fn deref(&self) -> &Self::Target {
        self.borrow
    }
}

impl<'a, T: ?Sized> GuardedBorrow<'a, T> {
    /// The [`guard`](Guard::guard) associated with this borrow.
    ///
    /// The type invariant of the guarded borrow ensures that the current value
    /// of [`borrow`](Self::borrow) satisfies this guard.
    #[logic(open, inline)]
    pub fn guard(self) -> Mapping<T, bool> {
        *self._guard
    }

    /// The final value of [`borrow`](Self::borrow).
    ///
    /// This final value is stored inside the guard (in a [`Snapshot`]),
    /// independently of `borrow`. It is used to ensure that you do not replace
    /// the value of borrow with one that has a different prophecy.
    #[logic(open, inline, prophetic)]
    pub fn prophecy(self) -> &'a T {
        pearlite! { &^*self._initial }
    }

    /// Create a new guarded borrow.
    ///
    /// The borrow contained in the result is guaranteed to satisfy the [`guard`](Guard::guard).
    #[requires(guard[*borrow])]
    #[ensures(result.borrow == borrow)]
    #[ensures(result.guard() == *guard)]
    #[check(ghost)]
    pub fn new(borrow: &'a mut T, guard: Snapshot<Mapping<T, bool>>) -> Self {
        Self { _initial: snapshot!(borrow), borrow, _guard: guard }
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
