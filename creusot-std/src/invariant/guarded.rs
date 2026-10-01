use crate::{logic::Mapping, prelude::*};

/// Guards that can be used in [`Guarded`].
pub trait Guard<T> {
    /// Property that must be satisfied by the end of `Guarded`.
    ///
    /// `initial` is the initial guarded value remembered by `Guarded`,
    /// `current` is the current guarded value (the `inner` field of `Guarded`).
    #[logic(prophetic)]
    fn guards(self, initial: T, current: T) -> bool;
}

/// Guard predicate under mutable references.
///
/// Notably, `G: GuardRef<T>` implies `G: Guard<&mut T>`
/// and `G: Guard<FullBorrow<T>>`.
pub trait GuardRef<T> {
    #[logic(prophetic)]
    fn guards_ref(self, x: T) -> bool;
}

impl<'a, G: GuardRef<T>, T> Guard<&'a mut T> for G {
    #[logic(open, prophetic, inline)]
    fn guards(self, initial: &'a mut T, current: &'a mut T) -> bool {
        pearlite! { self.guards_ref(*current) && ^initial == ^current }
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
/// The guard is represented by a value `guard: G` whose type implements the trait
/// [`Guard<T>`]. The relation [`guard.guards(inner, initial)`][Guard::guards]
/// is the property that must be satisfied when the guarded object disappears,
/// where `inner` is the current value of the guarded object, and `initial` is
/// its initial value when the `Guarded` object is created. The initial value is
/// used to guarantee that the guarded object is not replaced with another (it
/// may be mutated, but not replaced with another) using e.g., [`std::mem::swap`].
///
/// `Guarded` is typically used with a `T` mutable borrow. In this case,
/// `Guard<&mut T>` guarantees that the prophecies never change, and the
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
/// let guarded = Guarded::new_m(&mut x, snapshot!(|x: i32| x == 1i32));
/// // break the guard...
/// breaks_inv(&mut *guarded.inner);
/// // but restore it before we are done
/// *guarded.inner = 1;
/// ```
#[repr(transparent)]
#[intrinsic("guarded")]
pub struct Guarded<T, G: Guard<T>> {
    /// Payload of this `Guarded` value.
    pub inner: T,
    _guard: Snapshot<G>,
    _initial: Snapshot<T>,
}

impl<T, G: Guard<T>> Invariant for Guarded<T, G> {
    #[logic(open, prophetic, inline)]
    fn invariant(self) -> bool {
        pearlite! { (*self._guard).guards(*self._initial, self.inner) }
    }
}

impl<T, G: Guard<T>> Guarded<T, G> {
    #[logic(open, inline)]
    pub fn guard(self) -> G {
        pearlite! { *self._guard }
    }
}

impl<'a, T, G: GuardRef<T>> Guarded<&'a mut T, G> {
    /// Create a new guarded borrow.
    ///
    /// The borrow contained in the result is guaranteed to satisfy the
    /// [`guard`](Guard::guard) at the end of its lifetime. Thus, we get the
    /// guard for its prophecy.
    ///
    /// Note that the type of the second argument may not be inferred during
    /// compilation with rustc if it is directly constructed using
    /// the `snapshot!` macro. You may want to spell out the first type
    /// argument of `Guarded`, or use `Guarded::new_m` if the guard is a `Mapping`.
    #[trusted]
    #[requires(guard.guards_ref(*borrow))]
    #[ensures(result.inner == borrow)]
    #[ensures(result.guard() == *guard)]
    #[ensures(guard.guards_ref(^borrow))]
    #[check(ghost)]
    pub fn new(borrow: &'a mut T, guard: Snapshot<G>) -> Self {
        Self { inner: borrow, _guard: guard, _initial: snapshot!(borrow) }
    }
}

impl<'a, T> Guarded<&'a mut T, Mapping<T, bool>> {
    /// Variant of [`Guarded::new`] specialized with `Mapping` as the guard.
    #[requires(guard.guards_ref(*borrow))]
    #[ensures(result.inner == borrow)]
    #[ensures(result.guard() == *guard)]
    #[ensures(guard.guards_ref(^borrow))]
    #[check(ghost)]
    pub fn new_m(borrow: &'a mut T, guard: Snapshot<Mapping<T, bool>>) -> Self {
        Self::new(borrow, guard)
    }
}

impl<'a, T> Guarded<&'a mut Option<T>, IsSome> {
    #[trusted]
    #[check(ghost)]
    #[ensures(*result.inner == Some(*borrow))]
    #[ensures(^result.inner == Some(^borrow))]
    pub fn some(borrow: &'a mut T) -> Ghost<Self> {
        let _ = borrow;
        panic!("ghost only")
    }
}

impl<T> GuardRef<T> for Mapping<T, bool> {
    #[logic(open, inline)]
    fn guards_ref(self, x: T) -> bool {
        pearlite! { self[x] }
    }
}

/// Guard an `Option` that must remain `Some`.
pub struct IsSome;

impl<T> GuardRef<Option<T>> for IsSome {
    #[logic(open, inline)]
    fn guards_ref(self, x: Option<T>) -> bool {
        pearlite! { x != None }
    }
}
