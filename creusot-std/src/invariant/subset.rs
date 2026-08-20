use crate::prelude::*;
#[cfg(creusot)]
use crate::resolve::structural_resolve;
use core::ops::{Deref, DerefMut};

/// A type implements `InhabitedInvariants` when its type invariant is inhabited.
/// This is needed to define subset types.
pub trait InhabitedInvariant: Invariant + Sized {
    #[logic]
    #[ensures(result.invariant())]
    fn inhabits() -> Self;
}

/// A _subset_ type.
///
/// This the same as `T`, with one exception: the invariant for `T` will also
/// be verified in logic.
///
/// # Example
///
/// ```
/// # use creusot_std::{invariant::{InhabitedInvariant, Subset}, prelude::*};
/// struct Pair(i32);
/// impl Invariant for Pair {
///     #[logic] fn invariant(self) -> bool { self.0 % 2 == 0 }
/// }
/// impl InhabitedInvariant for Pair {
///     #[logic]
///     #[ensures(result.invariant())]
///     fn inhabits() -> Self { Self(0i32) }
/// }
///
/// #[logic]
/// fn pair_in_logic(x: Subset<Pair>) {
///     proof_assert!(x.0 % 2 == 0);
/// }
/// ```
#[repr(transparent)]
#[opaque]
pub struct Subset<T: InhabitedInvariant>(T);

impl<T: InhabitedInvariant + DeepModel> DeepModel for Subset<T> {
    type DeepModelTy = T::DeepModelTy;

    #[logic(inline)]
    fn deep_model(self) -> T::DeepModelTy {
        pearlite! { self.inner().deep_model() }
    }
}

impl<T: InhabitedInvariant> Subset<T> {
    #[trusted]
    #[logic(opaque)]
    #[ensures(result.invariant())]
    pub fn inner(self) -> T {
        dead
    }

    /// Create a new element of `Subset<T>` in logic.
    ///
    /// As per the [documentation of Subset](Subset), the returned value will
    /// satisfy `T`'s type invariant.
    #[trusted]
    #[logic(opaque)]
    #[requires(x.invariant())]
    #[ensures(result.inner() == x)]
    pub fn new_logic(x: T) -> Self {
        let _ = x;
        dead
    }

    /// Characterize that `Subset<T>` indeed contains a `T` (and only a `T`).
    ///
    /// # Example
    ///
    /// ```
    /// # use creusot_std::{invariant::Subset, prelude::*};
    /// #[requires(x == y.inner())]
    /// fn foo<T: InhabitedInvariant>(x: T, y: Subset<T>) {
    ///     let x = Subset::new(x);
    ///     let _ = snapshot!(Subset::<T>::inner_inj);
    ///     proof_assert!(x == y);
    /// }
    /// ```
    #[trusted]
    #[logic(opaque)]
    #[requires(self.inner() == other.inner())]
    #[ensures(self == other)]
    pub fn inner_inj(self, other: Self) {}

    /// Create a new element of `Subset<T>`.
    ///
    /// # Example
    ///
    /// ```
    /// # use creusot_std::{invariant::{InhabitedInvariant, Subset}, prelude::*};
    /// // Use the `Pair` type defined in `Subset`'s documentation
    /// # struct Pair(i32);
    /// # impl Invariant for Pair {
    /// #     #[logic] fn invariant(self) -> bool { self.0 % 2 == 0 } }
    /// # impl InhabitedInvariant for Pair {
    /// #     #[logic] #[ensures(result.invariant())]
    /// #     fn inhabits() -> Self { Self(0i32) } }
    ///
    /// let p = Subset::new(Pair(0));
    /// proof_assert!(p.inner().0 == 0i32);
    /// ```
    #[check(ghost)]
    #[trusted]
    #[ensures(result == Self::new_logic(x))]
    pub fn new(x: T) -> Self {
        Subset(x)
    }

    /// Unwrap the `Subset` to get the inner value.
    ///
    /// # Example
    ///
    /// ```
    /// # use creusot_std::{invariant::{InhabitedInvariant, Subset}, prelude::*};
    /// // Use the `Pair` type defined in `Subset`'s documentation
    /// # struct Pair(i32);
    /// # impl Invariant for Pair {
    /// #     #[logic] fn invariant(self) -> bool { self.0 % 2 == 0 } }
    /// # impl InhabitedInvariant for Pair {
    /// #     #[logic] #[ensures(result.invariant())]
    /// #     fn inhabits() -> Self { Self(0i32) } }
    ///
    /// fn changes_pair(p: &mut Subset<Pair>) { /* ... */ }
    ///
    /// let mut p = Subset::new(Pair(0));
    /// changes_pair(&mut p);
    /// let inner = p.into_inner();
    /// proof_assert!(inner.0 % 2 == 0);
    /// ```
    #[check(ghost)]
    #[trusted]
    #[ensures(result == self.inner())]
    pub fn into_inner(self) -> T {
        self.0
    }
}

impl<T: InhabitedInvariant> Deref for Subset<T> {
    type Target = T;

    #[check(ghost)]
    #[trusted]
    #[ensures(*result == self.inner())]
    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl<T: InhabitedInvariant> DerefMut for Subset<T> {
    #[check(ghost)]
    #[trusted]
    #[ensures(*result == self.inner())]
    #[ensures(^result == (^self).inner())]
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

impl<T: InhabitedInvariant + Clone> Clone for Subset<T> {
    #[ensures(T::clone.postcondition((&(self.inner()),), result.inner()))]
    fn clone(&self) -> Self {
        snapshot! { Self::inner_inj };
        Self::new(self.deref().clone())
    }
}

impl<T: InhabitedInvariant + Copy> Copy for Subset<T> {}

impl<T: InhabitedInvariant> Resolve for Subset<T> {
    #[logic(open, prophetic, inline)]
    fn resolve(self) -> bool {
        pearlite! { resolve(self.inner()) }
    }

    #[trusted]
    #[logic(prophetic)]
    #[requires(structural_resolve(self))]
    #[ensures(self.resolve())]
    fn resolve_coherence(self) {}
}

impl<T: InhabitedInvariant + DeepModel + PartialEq> PartialEq for Subset<T> {
    #[trusted]
    #[ensures(result == (self.deep_model() == rhs.deep_model()))]
    fn eq(&self, rhs: &Self) -> bool {
        self.0 == rhs.0
    }
}

impl<T: InhabitedInvariant + DeepModel + Eq> Eq for Subset<T> {}
