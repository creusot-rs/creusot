//! Define local invariants.
//!
//! [Local invariants](LocalInvariant) are not the same as [type invariants](Invariant): they
//! allow the use of a shared piece of data to be used in the invariant (see
//! [`Protocol`]), but in return they impose a much more restricted access to
//! the underlying data, as well as the use of [`Tokens`].
//!
//! # Example
//!
//! Building a simplified `Cell`, that only asserts its content's type invariant.
//! ```
//! # use creusot_contracts::{
//! #     cell::{PermCell, PermCellOwn},
//! #     ghost::local_invariant::{LocalInvariant, Protocol, Tokens, declare_namespace},
//! #     logic::Id,
//! #     prelude::*,
//! # };
//! declare_namespace! { PERMCELL }
//!
//! /// A cell that simply asserts its content's type invariant.
//! pub struct CellInv<T: Invariant> {
//!     data: PermCell<T>,
//!     permission: Ghost<LocalInvariant<PermCellLocalInv<T>>>,
//! }
//! impl<T: Invariant> Invariant for CellInv<T> {
//!     #[logic]
//!     fn invariant(self) -> bool {
//!         self.permission.namespace() == PERMCELL() && self.permission.public() == self.data.id()
//!     }
//! }
//!
//! struct PermCellLocalInv<T>(PermCellOwn<T>);
//! impl<T: Invariant> Protocol for PermCellLocalInv<T> {
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
//!         LocalInvariant::open(self.permission.borrow(), tokens, move |perm| unsafe {
//!             *self.data.borrow_mut(ghost!(&mut perm.into_inner().0)) = x
//!         })
//!     }
//! }
//! ```
//!
//! # Explicit tokens
//!
//! For now, [`Tokens`] must be explicitely passed to [`open`](LocalInvariant::open).
//! We plan to relax this limitation at some point.

use crate::{logic::Set, prelude::*};
use std::{cell::UnsafeCell, marker::PhantomData};

/// Declare a new namespace.
///
/// # Example
///
/// ```rust
/// use creusot_contracts::{ghost::local_invariant::{declare_namespace, Namespace}, logic::Set, prelude::*};
/// declare_namespace! { A }
///
/// #[requires(ns.contains(A()))]
/// fn foo(ns: Ghost<&mut Set<Namespace>>) { /* ... */ }
/// ```
pub use base_macros::declare_namespace;

/// The type of _namespaces_ of associated with local invariants.
///
/// Can be declared with the [`declare_namespace`] macro, and then attached to a local
/// invariant when creating it with [`LocalInvariant::new`].
#[intrinsic("namespace")]
pub struct Namespace(());

/// Invariant tokens.
///
/// This is given at the start of the program, and must be passed along to
/// [LocalInvariant::open] to prevent opening invariant reentrantly.
///
/// # Tokens and `open`
///
/// Tokens are used to avoid reentrency in [`open`](LocalInvariant::open).
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
pub struct Tokens<'a>(PhantomData<&'a ()>);

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
    /// # use creusot_contracts::{ghost::local_invariant::Tokens, prelude::*};
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
        Tokens(PhantomData)
    }

    /// Split the tokens in two, so that it can be used to access independant invariants.
    ///
    /// # Example
    ///
    /// ```
    /// # use creusot_contracts::{ghost::local_invariant::{declare_namespace, Tokens}, prelude::*};
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
    #[allow(unused_variables)]
    pub fn split<'a>(&'a mut self, ns: Snapshot<Namespace>) -> (Tokens<'a>, Tokens<'a>) {
        (Tokens(PhantomData), Tokens(PhantomData))
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

/// A ghost structure, that holds a piece of data (`T`) together with an
/// [protocol](Protocol).
#[opaque]
pub struct LocalInvariant<T: Protocol> {
    value: UnsafeCell<T>,
}

/// A variant of [`Invariant`] for use in [`LocalInvariant`]s.
///
/// This allows to specify an invariant that depends on some [public data](LocalInvariant::public).
pub trait Protocol {
    type Public;

    #[logic(prophetic)]
    fn protocol(self, data: Self::Public) -> bool;
}

/// Define method call syntax for [`LocalInvariant::open`].
pub trait LocalInvariantExt<'a> {
    type Inner: 'a;

    /// Alias for [`LocalInvariant::open`], to use method call syntax (`inv.open(...)`).
    #[requires(false)]
    fn open<A, F>(self, tokens: Ghost<Tokens<'a>>, f: F) -> A
    where
        F: FnOnce(Ghost<&'a mut Self::Inner>) -> A;
}

impl<'a, T: Protocol> LocalInvariantExt<'a> for Ghost<&'a LocalInvariant<T>> {
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
        LocalInvariant::open(self, tokens, f)
    }
}

impl<'a, T> LocalInvariantExt<'a> for Ghost<&'a T>
where
    T: std::ops::Deref,
    Ghost<&'a T::Target>: LocalInvariantExt<'a>,
{
    type Inner = <Ghost<&'a T::Target> as LocalInvariantExt<'a>>::Inner;

    #[requires(T::deref.precondition((*self,)))]
    #[requires(forall<this> T::deref.postcondition((*self,), this) ==>
        <Ghost<&'a T::Target> as LocalInvariantExt<'a>>::open.precondition((Ghost::new_logic(this), tokens, f))
    )]
    #[ensures(exists<this> T::deref.postcondition((*self,), this) &&
        <Ghost<&'a T::Target> as LocalInvariantExt<'a>>::open.postcondition((Ghost::new_logic(this), tokens, f), result)
    )]
    fn open<A, F>(self, tokens: Ghost<Tokens<'a>>, f: F) -> A
    where
        F: FnOnce(Ghost<&'a mut Self::Inner>) -> A,
    {
        let this: Ghost<&T::Target> = ghost!(&self);
        this.open(tokens, f)
    }
}

impl<'a, L> LocalInvariantExt<'a> for &'a Ghost<L>
where
    Ghost<&'a L>: LocalInvariantExt<'a>,
{
    type Inner = <Ghost<&'a L> as LocalInvariantExt<'a>>::Inner;

    #[requires(<Ghost<&'a L> as LocalInvariantExt<'a>>::open.precondition((Ghost::new_logic(&**self), tokens, f)))]
    #[ensures(<Ghost<&'a L> as LocalInvariantExt<'a>>::open.postcondition((Ghost::new_logic(&**self), tokens, f), result))]
    fn open<A, F>(self, tokens: Ghost<Tokens<'a>>, f: F) -> A
    where
        F: FnOnce(Ghost<&'a mut Self::Inner>) -> A,
    {
        self.borrow().open(tokens, f)
    }
}

impl<T: Protocol> LocalInvariant<T> {
    /// Construct a `LocalInvariant`
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
        #[allow(unused)] public: Snapshot<T::Public>,
        #[allow(unused)] namespace: Snapshot<Namespace>,
    ) -> Ghost<Self> {
        ghost!(Self { value: UnsafeCell::new(value.into_inner()) })
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
    #[ensures(exists<t: Ghost<&mut T>> t.protocol(this.public()) && f.postcondition_once((t,), result))]
    pub fn open<'a, A>(
        this: Ghost<&'a Self>,
        tokens: Ghost<Tokens<'a>>,
        f: impl FnOnce(Ghost<&'a mut T>) -> A,
    ) -> A {
        let _ = tokens;
        // SAFETY: this operation happens in a ghost block, meaning it only
        // make sense when compiling with creusot: in this case, Creusot will
        // make sure that this is in fact safe.
        let borrow = ghost!(unsafe { &mut *this.value.get() });
        f(borrow)
    }

    /// Open the invariant to get the data stored inside, immutably.
    /// This allows reentrant access to the invariant.
    #[trusted]
    #[requires(tokens.contains(self.namespace()))]
    #[ensures(result.protocol(self.public()))]
    #[check(ghost)]
    pub fn open_const<'a>(&'a self, tokens: &'a Tokens) -> &'a T {
        let _ = tokens;
        unsafe { &*self.value.get() }
    }
}
