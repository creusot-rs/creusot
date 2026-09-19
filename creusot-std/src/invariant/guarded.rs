use crate::{
    logic::{Mapping, ops::Fin},
    prelude::*,
};

#[cfg(creusot)]
use crate::logic::any;

pub trait GuardedRelation {
    #[logic(prophetic)]
    fn rel(self, other: Self) -> bool;
}

impl<T: Fin> GuardedRelation for T {
    #[logic(open, prophetic, inline)]
    fn rel(self, other: Self) -> bool {
        pearlite! { ^self == ^other }
    }
}

/// `Guarded` is a wrapper around an object of type `T`, which makes sure that a
/// guard (a predicate on `T`) is satisfied when the guarded object disappears.
/// It works by making the guard part of the type invariant of `Guarded`,
/// and uses some internal Creusot machinery to ensure that the guard
/// never changes during the lifetime of the `Guarded` object.
///
/// As such, the guard can be broken locally, but it must be restored before the
/// `Guarded` object is dropped, passed as a parameter, returned or when a
/// borrow of the `Guarded` is resolved.
///
/// The type `T` must implement `GuardedRelation`, which is a way to guarantee
/// that the guarded object is not replaced with another (it may be mutated, but
/// not replaced with another) using e.g., [`std::mem::swap`].
///
/// `Guarded` is typically used with a `T` mutable borrow. In this case,
/// `GuardedRelation` guarantees that the prophecies never change, and the
/// guard typically guarantees that the final value of the borrow satisfies
/// some property. Other uses include types that behave like mutable borrows,
/// such as `FullBorrow`.
///
/// # Example
///
/// ```
/// use creusot_std::prelude::*;
/// use creusot_std::invariant::Guarded;
///
/// #[ensures(^b == 0i32)]
/// fn breaks_inv(b: &mut i32) { *b = 0; }
///
/// let mut x = 1;
/// let guarded = Guarded::new(&mut x, snapshot!(|x: i32| x == 1i32));
/// // break the guard...
/// breaks_inv(&mut *guarded.inner);
/// // but restore it before we are done
/// *guarded.inner = 1;
/// ```
#[repr(transparent)]
#[intrinsic("guarded")]
pub struct Guarded<T: GuardedRelation> {
    /// Payload of this `Guarded` value.
    pub inner: T,
    _guard: Snapshot<Mapping<T, bool>>,
    _initial: Snapshot<T>,
}

impl<T: GuardedRelation> Invariant for Guarded<T> {
    #[logic(open, prophetic, inline)]
    fn invariant(self) -> bool {
        pearlite! { self.guard()[self.inner] && self.inner.rel(*self._initial) }
    }
}

impl<T: GuardedRelation> Guarded<T> {
    /// The [`guard`](Guard::guard) associated with this `Guarded` value.
    #[logic(open, inline)]
    pub fn guard(self) -> Mapping<T, bool> {
        *self._guard
    }
}

impl<'a, T: ?Sized> Guarded<&'a mut T> {
    /// Create a new guarded borrow.
    ///
    /// The borrow contained in the result is guaranteed to satisfy the
    /// [`guard`](Guard::guard) at the end of its lifetime. Thus, we get the
    /// guard for its prophecy.
    #[trusted]
    #[requires(guard[*borrow])]
    #[ensures(result.inner == borrow)]
    #[ensures(forall<bor: &mut T> result.guard()[bor] == guard[*bor])]
    #[ensures(guard[^borrow])]
    #[check(ghost)]
    pub fn new(borrow: &'a mut T, #[allow(unused)] guard: Snapshot<Mapping<T, bool>>) -> Self {
        Self { inner: borrow, _guard: snapshot!(any()), _initial: snapshot!(any()) }
    }
}
