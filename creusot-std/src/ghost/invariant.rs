//! Resource invariants.
//!
//! Resource invariants allow the use of a shared piece of data to be used in
//! the invariant (see [`Protocol`]), but in return they impose a much more
//! restricted access to the underlying data, as well as the use of [`Tokens`].
//!
//! [Atomic invariants](AtomicInvariant) are used to specify concurrent
//! operations.
//!
//! [Non-atomic invariants](NonAtomicInvariant) are used to specify thread-local
//! operations.
//!
//! Not to be confused with [loop invariants][crate::macros::invariant] or
//! [type invariants][crate::invariant::Invariant].
//!
//! # Example
//!
//! Building a simplified `Cell`, that only asserts its content's type invariant.
//! ```
//! # use creusot_std::{
//! #     cell::PermCell,
//! #     ghost::{
//! #         invariant::{NonAtomicInvariant, Protocol, Tokens, declare_namespace},
//! #         perm::Perm,
//! #     },
//! #     logic::Id,
//! #     prelude::*,
//! # };
//! declare_namespace! { PERMCELL }
//!
//! /// A cell that simply asserts its content's type invariant.
//! pub struct CellInv<T: Invariant> {
//!     data: PermCell<T>,
//!     permission: Ghost<NonAtomicInvariant<PermCellNAInv<T>>>,
//! }
//! impl<T: Invariant> Invariant for CellInv<T> {
//!     #[logic]
//!     fn invariant(self) -> bool {
//!         self.permission.namespace() == PERMCELL() && self.permission.public() == self.data.id()
//!     }
//! }
//!
//! struct PermCellNAInv<T>(Box<Perm<PermCell<T>>>);
//! impl<T: Invariant> Protocol for PermCellNAInv<T> {
//!     type Public = Id;
//!
//!     #[logic]
//!     fn protocol(self, id: Id) -> bool {
//!         self.0.id() == id
//!     }
//! }
//!
//! impl<T: Invariant> CellInv<T> {
//!     #[requires(tokens.contains(PERMCELL()))]
//!     pub fn write(&self, x: T, tokens: Ghost<Tokens>) {
//!         NonAtomicInvariant::open(self.permission.borrow(), tokens, move |perm| unsafe {
//!             *self.data.borrow_mut(ghost!(&mut perm.into_inner().0)) = x
//!         })
//!     }
//! }
//! ```
//!
//! # Explicit tokens
//!
//! For now, [`Tokens`] must be explicitely passed to [`open`](NonAtomicInvariant::open).
//! We plan to relax this limitation at some point.

#![allow(unused_variables)]

use crate::{
    ghost::{FnGhost, Plain},
    logic::Set,
    prelude::*,
};
use core::marker::PhantomData;

/// Declare a new namespace.
///
/// # Example
///
/// ```rust
/// use creusot_std::{ghost::invariant::{declare_namespace, Namespace}, logic::Set, prelude::*};
/// declare_namespace! { A }
///
/// #[requires(ns.contains(A()))]
/// fn foo(ns: Ghost<&mut Set<Namespace>>) { /* ... */ }
/// ```
pub use base_macros::declare_namespace;

/// The type of _namespaces_ of associated with non-atomic invariants.
///
/// Can be declared with the [`declare_namespace`] macro, and then attached to a non-atomic
/// invariant when creating it with [`NonAtomicInvariant::new`].
#[intrinsic("namespace")]
pub struct Namespace(());

impl Clone for Namespace {
    #[check(ghost)]
    #[ensures(result == *self)]
    fn clone(&self) -> Self {
        *self
    }
}
impl Copy for Namespace {}

impl Plain for Namespace {
    #[trusted]
    #[ensures(*result == *snap)]
    #[check(ghost)]
    #[allow(unused_variables)]
    fn into_ghost(snap: Snapshot<Self>) -> Ghost<Self> {
        Ghost::conjure()
    }
}

/// Invariant tokens.
///
/// This is given at the start of the program, and must be passed along to
/// [NonAtomicInvariant::open] to prevent opening invariant reentrantly.
///
/// # Tokens and `open`
///
/// Tokens are used to avoid reentrency in [`open`](NonAtomicInvariant::open).
/// To ensure this, `Tokens` acts as a special kind of mutable borrow : only
/// one may exist at a given point in the program, preventing multiple calls to
/// `open` with the same namespace. This is the reason this type has a lifetime
/// attached to it.
///
/// Note that after the execution of `open`, the token that was used is
/// restored. Because of this, we never need to talk about the 'final' value
/// of this borrow, because it never differs from the current value (in places
/// where we can use it).
///
/// To help passing it into functions, it may be [reborrowed](Self::reborrow),
/// similarly to a normal borrow.
#[opaque]
// `*mut ()` so that Tokens are neither Send nor Sync
pub struct Tokens<'a>(PhantomData<&'a ()>, PhantomData<*mut ()>);

impl Tokens<'_> {
    /// Get the underlying set of namespaces of this token.
    ///
    /// Also accessible via the [`view`](View::view) (`@`) operator.
    #[logic(opaque)]
    pub fn namespaces(self) -> Set<Namespace> {
        dead
    }

    /// Get the tokens for all the namespaces.
    ///
    /// This is only callable _once_, in `main`.
    #[trusted]
    #[ensures(forall<ns: Namespace> result.contains(ns))]
    #[intrinsic("tokens_new")]
    #[check(ghost)]
    pub fn new() -> Ghost<Self> {
        Ghost::conjure()
    }

    /// Reborrow the token, allowing it to be reused later.
    ///
    /// # Example
    /// ```
    /// # use creusot_std::{ghost::invariant::Tokens, prelude::*};
    /// fn foo(tokens: Ghost<Tokens>) {}
    /// fn bar(tokens: Ghost<Tokens>) {}
    /// fn baz(mut tokens: Ghost<Tokens>) {
    ///     foo(ghost!(tokens.reborrow()));
    ///     bar(tokens);
    /// }
    /// ```
    #[trusted]
    #[ensures(result == *self && ^self == *self)]
    #[check(ghost)]
    pub fn reborrow<'a>(&'a mut self) -> Tokens<'a> {
        Tokens(PhantomData, PhantomData)
    }

    /// Split the tokens in two, so that it can be used to access independant invariants.
    ///
    /// # Example
    ///
    /// ```
    /// # use creusot_std::{ghost::invariant::{declare_namespace, Tokens}, prelude::*};
    /// declare_namespace! { FOO }
    /// declare_namespace! { BAR }
    ///
    /// // the lifetime 'locks' the namespace
    /// #[requires(tokens.contains(FOO()))]
    /// fn foo<'a>(tokens: Ghost<Tokens<'a>>) -> &'a i32 {
    /// # todo!()
    ///     // access some invariant to get the reference
    /// }
    /// #[requires(tokens.contains(BAR()))]
    /// fn bar(tokens: Ghost<Tokens>) {}
    ///
    /// #[requires(tokens.contains(FOO()) && tokens.contains(BAR()))]
    /// fn baz(mut tokens: Ghost<Tokens>) -> i32 {
    ///      let (ns_foo, ns_bar) = ghost!(tokens.split(snapshot!(FOO()))).split();
    ///      let x = foo(ns_foo);
    ///      bar(ns_bar);
    ///      *x
    /// }
    /// ```
    #[trusted]
    #[requires(self.contains(*ns))]
    #[ensures(^self == *self)]
    #[ensures(result.0.contains(*ns))]
    #[ensures(result.1.namespaces() == self.namespaces().remove(*ns))]
    #[check(ghost)]
    pub fn split<'a>(&'a mut self, ns: Snapshot<Namespace>) -> (Tokens<'a>, Tokens<'a>) {
        (Tokens(PhantomData, PhantomData), Tokens(PhantomData, PhantomData))
    }

    #[logic(open)]
    pub fn contains(self, namespace: Namespace) -> bool {
        self.namespaces().contains(namespace)
    }
}

impl View for Tokens<'_> {
    type ViewTy = Set<Namespace>;
    #[logic(open, inline)]
    fn view(self) -> Set<Namespace> {
        self.namespaces()
    }
}

/// A variant of [`Invariant`] for use in [`AtomicInvariant`]s and [`NonAtomicInvariant`]s.
///
/// This allows to specify an invariant that depends on some public data
/// (`AtomicInvariant::public`, `NonAtomicInvariant::public`).
pub trait Protocol {
    type Public;

    #[logic(prophetic)]
    fn protocol(self, data: Self::Public) -> bool;
}

#[opaque]
pub struct AtomicInvariant<T>(PhantomData<*mut T>);

unsafe impl<T: Send> Sync for AtomicInvariant<T> {}

impl<T: Protocol> AtomicInvariant<T> {
    /// Construct a `AtomicInvariant`
    ///
    /// # Parameters
    /// - `value`: the actual data contained in the invariant. Use [`Self::open`] to
    /// access it. Also called the 'private' part of the invariant.
    /// - `public`: the 'public' part of the invariant.
    /// - `namespace`: the namespace of the invariant.
    ///   This is required to avoid [open](Self::open)ing the same invariant twice.
    #[trusted]
    #[requires(value.protocol(*public))]
    #[ensures(result.public() == *public)]
    #[ensures(result.namespace() == *namespace)]
    #[check(ghost)]
    pub fn new(
        value: Ghost<T>,
        public: Snapshot<T::Public>,
        namespace: Snapshot<Namespace>,
    ) -> Ghost<Self> {
        Ghost::conjure()
    }

    /// Get the namespace associated with this invariant.
    #[logic(opaque)]
    pub fn namespace(self) -> Namespace {
        dead
    }

    /// Get the 'public' part of this invariant.
    #[logic(opaque)]
    pub fn public(self) -> T::Public {
        dead
    }

    /// Gives the actual invariant held by the [`AtomicInvariant`].
    #[trusted]
    #[ensures(result.protocol(self.public()))]
    #[check(ghost)]
    pub fn into_inner(self) -> T {
        panic!("Should not be called outside ghost code")
    }

    /// Open the invariant to get the data stored inside.
    ///
    /// This will call the closure `f` with the inner data. You must restore the
    /// contained [`Protocol`] before returning from the closure.
    ///
    /// NOTE: This function can only be called from ghost code, because atomic
    /// invariants are always wrapped in `Ghost`. This guarantees atomicity.
    #[trusted]
    #[requires(tokens.contains(self.namespace()))]
    #[requires(forall<t: &mut T> t.protocol(self.public()) && inv(t) ==>
        f.precondition((t,)) &&
        // f must restore the invariant
        (forall<res: A> f.postcondition_once((t,), res) ==> (^t).protocol(self.public())))]
    #[ensures(exists<t: &mut T> inv(t) && t.protocol(self.public()) && f.postcondition_once((t,), result))]
    #[check(ghost)]
    pub fn open<A>(&self, tokens: Tokens, f: impl FnGhost + for<'a> FnOnce(&'a mut T) -> A) -> A {
        panic!("Should not be called outside ghost code")
    }
}

/// A ghost structure, that holds a piece of data (`T`) together with an
/// [protocol](Protocol).
///
/// # Note
///
/// `NonAtomicInvariant` is not `Sync`, and is invariant in the underlying data.
/// - not `Sync` precisely because it is non-atomic, so access to the data is unsyncronized
/// - invariant because it gives access to a mutable borrow of this data.
#[opaque]
pub struct NonAtomicInvariant<T: Protocol>(PhantomData<*mut T>);

/// Define method call syntax for [`NonAtomicInvariant::open`].
pub trait NonAtomicInvariantExt<'a> {
    type Inner: 'a;

    /// Alias for [`NonAtomicInvariant::open`], to use method call syntax (`inv.open(...)`).
    #[requires(false)]
    fn open<A, F>(self, tokens: Ghost<Tokens<'a>>, f: F) -> A
    where
        F: FnOnce(Ghost<&'a mut Self::Inner>) -> A;
}

impl<'a, T: Protocol> NonAtomicInvariantExt<'a> for Ghost<&'a NonAtomicInvariant<T>> {
    type Inner = T;

    #[requires(tokens.contains(self.namespace()))]
    #[requires(forall<t: Ghost<&mut T>> (**t).protocol(self.public()) && inv(t) ==>
        f.precondition((t,)) &&
        // f must restore the invariant
        (forall<res: A> f.postcondition_once((t,), res) ==> (^t).protocol(self.public())))]
    #[ensures(exists<t: Ghost<&mut T>> t.protocol(self.public()) && f.postcondition_once((t,), result))]
    fn open<A, F>(self, tokens: Ghost<Tokens<'a>>, f: F) -> A
    where
        F: FnOnce(Ghost<&'a mut Self::Inner>) -> A,
    {
        NonAtomicInvariant::open(self, tokens, f)
    }
}

impl<'a, T> NonAtomicInvariantExt<'a> for Ghost<&'a T>
where
    T: core::ops::Deref,
    Ghost<&'a T::Target>: NonAtomicInvariantExt<'a>,
{
    type Inner = <Ghost<&'a T::Target> as NonAtomicInvariantExt<'a>>::Inner;

    #[requires(T::deref.precondition((*self,)))]
    #[requires(forall<this> T::deref.postcondition((*self,), this) ==>
        <Ghost<&'a T::Target> as NonAtomicInvariantExt<'a>>::open.precondition((Ghost::new_logic(this), tokens, f))
    )]
    #[ensures(exists<this> T::deref.postcondition((*self,), this) &&
        <Ghost<&'a T::Target> as NonAtomicInvariantExt<'a>>::open.postcondition((Ghost::new_logic(this), tokens, f), result)
    )]
    fn open<A, F>(self, tokens: Ghost<Tokens<'a>>, f: F) -> A
    where
        F: FnOnce(Ghost<&'a mut Self::Inner>) -> A,
    {
        let this: Ghost<&T::Target> = ghost!(&self);
        this.open(tokens, f)
    }
}

impl<'a, L> NonAtomicInvariantExt<'a> for &'a Ghost<L>
where
    Ghost<&'a L>: NonAtomicInvariantExt<'a>,
{
    type Inner = <Ghost<&'a L> as NonAtomicInvariantExt<'a>>::Inner;

    #[requires(<Ghost<&'a L> as NonAtomicInvariantExt<'a>>::open.precondition((Ghost::new_logic(&**self), tokens, f)))]
    #[ensures(<Ghost<&'a L> as NonAtomicInvariantExt<'a>>::open.postcondition((Ghost::new_logic(&**self), tokens, f), result))]
    fn open<A, F>(self, tokens: Ghost<Tokens<'a>>, f: F) -> A
    where
        F: FnOnce(Ghost<&'a mut Self::Inner>) -> A,
    {
        self.borrow().open(tokens, f)
    }
}

impl<T: Protocol> NonAtomicInvariant<T> {
    /// Construct a `NonAtomicInvariant`
    ///
    /// # Parameters
    /// - `value`: the actual data contained in the invariant. Use [`Self::open`] to
    /// access it. Also called the 'private' part of the invariant.
    /// - `public`: the 'public' part of the invariant.
    /// - `namespace`: the namespace of the invariant.
    ///   This is required to avoid [open](Self::open)ing the same invariant twice.
    #[trusted]
    #[requires(value.protocol(*public))]
    #[ensures(result.public() == *public)]
    #[ensures(result.namespace() == *namespace)]
    #[check(ghost)]
    pub fn new(
        value: Ghost<T>,
        public: Snapshot<T::Public>,
        namespace: Snapshot<Namespace>,
    ) -> Ghost<Self> {
        Ghost::conjure()
    }

    /// Gives the actual invariant held by the [`NonAtomicInvariant`].
    #[trusted]
    #[ensures(result.protocol(self.public()))]
    #[check(ghost)]
    pub fn into_inner(self) -> T {
        panic!("Should not be called outside ghost code")
    }

    /// Get the namespace associated with this invariant.
    #[logic(opaque)]
    pub fn namespace(self) -> Namespace {
        dead
    }

    /// Get the 'public' part of this invariant.
    #[logic(opaque)]
    pub fn public(self) -> T::Public {
        dead
    }

    /// Open the invariant to get the data stored inside.
    ///
    /// This will call the closure `f` with the inner data. You must restore the
    /// contained [`Protocol`] before returning from the closure.
    #[trusted]
    #[requires(tokens.contains(this.namespace()))]
    #[requires(forall<t: Ghost<&mut T>> t.protocol(this.public()) && inv(t) ==>
        f.precondition((t,)) &&
        // f must restore the invariant
        (forall<res: A> f.postcondition_once((t,), res) ==> (^t).protocol(this.public())))]
    #[ensures(exists<t: Ghost<&mut T>> inv(t) && t.protocol(this.public()) && f.postcondition_once((t,), result))]
    pub fn open<'a, A>(
        this: Ghost<&'a Self>,
        tokens: Ghost<Tokens<'a>>,
        f: impl FnOnce(Ghost<&'a mut T>) -> A,
    ) -> A {
        f(Ghost::conjure())
    }

    /// Open the invariant to get the data stored inside, immutably.
    /// This allows reentrant access to the invariant.
    #[trusted]
    #[requires(tokens.contains(self.namespace()))]
    #[ensures(result.protocol(self.public()))]
    #[check(ghost)]
    pub fn open_const<'a>(&'a self, tokens: &'a Tokens) -> &'a T {
        panic!("Should not be called outside ghost code")
    }
}
