//! Define local invariants.
//!
//! [Local invariants](LocalInvariant) are not the same as [type invariants](Invariant): they
//! allow the use of a shared piece of data to be used in the invariant (see
//! [`LocalInvariantSpec`]), but in return they impose a much more restricted access to
//! the underlying data, as well as the use of [`Namespaces`].
//!
//! # Example
//!
//! Building a simplified `Cell`, that only asserts its content's type invariant.
//! ```
//! # use creusot_contracts::{
//! #     local_invariant::{LocalInvariant, LocalInvariantSpec, Namespaces, declare_namespace},
//! #     logic::Id,
//! #     pcell::{PCell, PCellOwn},
//! #     *,
//! # };
//! declare_namespace! { PCELL }
//!
//! /// A cell that simply asserts its content's type invariant.
//! pub struct CellInv<T: Invariant> {
//!     data: PCell<T>,
//!     permission: Ghost<LocalInvariant<PCellLocalInv<T>>>,
//! }
//! impl<T: Invariant> Invariant for CellInv<T> {
//!     #[logic]
//!     fn invariant(self) -> bool {
//!         self.permission.namespace() == PCELL() && self.permission.public() == self.data.id()
//!     }
//! }
//!
//! struct PCellLocalInv<T>(PCellOwn<T>);
//! impl<T: Invariant> LocalInvariantSpec for PCellLocalInv<T> {
//!     type Public = Id;
//!
//!     #[logic]
//!     fn invariant_with_data(self, id: Id) -> bool {
//!         self.0.id() == id
//!     }
//! }
//!
//! impl<T: Invariant> CellInv<T> {
//!     #[requires(namespaces.contains(PCELL()))]
//!     pub fn write(&self, x: T, namespaces: Ghost<Namespaces>) {
//!         LocalInvariant::open(self.permission.borrow(), namespaces, move |perm| unsafe {
//!             *self.data.borrow_mut(ghost!(&mut perm.into_inner().0)) = x
//!         })
//!     }
//! }
//! ```
//!
//! # Explicit namespaces
//!
//! For now, [`Namespaces`] must be explicitely passed to [`open`](LocalInvariant::open).
//! We plan to relax this limitation at some point.

use crate::{logic::Set, *};
use ::std::cell::UnsafeCell;

/// Declare a new namespace.
///
/// # Example
///
/// ```rust
/// use creusot_contracts::{*, local_invariant::{declare_namespace, Namespace}, logic::Set};
/// declare_namespace! { A }
///
/// #[requires(ns.contains(A()))]
/// fn foo(ns: Ghost<&mut Set<Namespace>>) { /* ... */ }
/// ```
pub use base_macros::declare_namespace;

/// The type of _namespaces_ associated with local invariants.
///
/// Can be declared with the [`declare_namespace`] macro, and then attached to a local
/// invariant when creating it with [`LocalInvariant::new`].
#[cfg_attr(creusot, rustc_diagnostic_item = "namespace_ty")]
#[trusted] // This type has a very special translation.
pub struct Namespace(());

/// A collection of namespaces.
///
/// This is given at the start of the program, and must be passed along to [LocalInvariant::open].
///
/// # Namespaces and `open`
///
/// Namespaces are used to avoid reentrency in [`open`](LocalInvariant::open).
/// To ensure this, `Namespaces` acts as a special kind of mutable borrow : only
/// one may exist at a given point in the program, preventing multiple calls to
/// `open` with the same namespace. This is the reason this type has a lifetime
/// attached to it.
///
/// Note that after the execution of `open`, the namespace that was used is
/// restored. Because of this, we never need to talk about the 'final' value
/// of this borrow, because it never differs from the current value (in places
/// where we can use it).
///
/// To help passing it into functions, it may be [reborrowed](Self::reborrow),
/// similarly to a normal borrow.
#[trusted]
pub struct Namespaces<'a>(::std::marker::PhantomData<&'a ()>);

impl Namespaces<'_> {
    /// Get the underlying set of namespaces.
    ///
    /// Also accessible via the [`view`](View::view) (`@`) operator.
    #[trusted]
    #[logic]
    pub fn namespaces(self) -> Set<Namespace> {
        dead
    }

    /// Reborrow the namespace, allowing it to be reused later.
    ///
    /// # Example
    /// ```
    /// # use creusot_contracts::{*, local_invariant::Namespaces};
    /// fn foo(namespaces: Ghost<Namespaces>) {}
    /// fn bar(namespaces: Ghost<Namespaces>) {}
    /// fn baz(mut namespaces: Ghost<Namespaces>) {
    ///     foo(ghost!(namespaces.reborrow()));
    ///     bar(namespaces);
    /// }
    /// ```
    #[trusted]
    #[ensures((*self).namespaces() == result.namespaces())]
    #[ensures((^self).namespaces() == result.namespaces())]
    #[check(ghost)]
    pub fn reborrow(&mut self) -> Namespaces {
        Namespaces(::std::marker::PhantomData)
    }

    #[logic]
    #[open]
    pub fn contains(self, namespace: Namespace) -> bool {
        self.namespaces().contains(namespace)
    }
}

impl View for Namespaces<'_> {
    type ViewTy = Set<Namespace>;
    #[logic]
    #[open]
    fn view(self) -> Set<Namespace> {
        self.namespaces()
    }
}

/// A ghost structure, that holds a piece of data (`T`) together with an
/// [invariant](LocalInvariantSpec).
#[trusted]
pub struct LocalInvariant<T: LocalInvariantSpec> {
    value: UnsafeCell<T>,
}

/// A variant of [`Invariant`] for use in [`LocalInvariant`]s.
///
/// This allows to specify an invariant that depends on some [public data](LocalInvariant::public).
pub trait LocalInvariantSpec {
    type Public;

    #[logic(prophetic)]
    fn invariant_with_data(self, data: Self::Public) -> bool;
}

/// Define method call syntax for [`LocalInvariant::open`].
pub trait LocalInvariantExt<'a> {
    type Inner: 'a;

    /// Alias for [`LocalInvariant::open`], to use method call syntax (`inv.open(...)`).
    #[requires(false)]
    #[ensures(true)]
    #[check(ghost)]
    fn open<A, F>(self, namespaces: Ghost<Namespaces<'a>>, f: F) -> A
    where
        F: FnOnce(Ghost<&'a mut Self::Inner>) -> A;
}

impl<'a, T: LocalInvariantSpec> LocalInvariantExt<'a> for Ghost<&'a LocalInvariant<T>> {
    type Inner = T;

    #[requires(namespaces@.contains(self.namespace()))]
    #[requires(forall<t: Ghost<&mut T>> (**t).invariant_with_data(self.public()) && inv(t) ==>
        f.precondition((t,)) &&
        // f must restore the invariant
        (forall<res: A> f.postcondition_once((t,), res) ==> (^*t).invariant_with_data(self.public())))]
    #[ensures(exists<t: Ghost<&mut T>> (**t).invariant_with_data(self.public()) && f.postcondition_once((t,), result))]
    #[check(ghost)]
    fn open<A, F>(self, namespaces: Ghost<Namespaces<'a>>, f: F) -> A
    where
        F: FnOnce(Ghost<&'a mut Self::Inner>) -> A,
    {
        LocalInvariant::open(self, namespaces, f)
    }
}

impl<T: LocalInvariantSpec> LocalInvariant<T> {
    /// Construct a `LocalInvariant`
    ///
    /// # Parameters
    /// - `value`: the actual data contained in the invariant. Use [`Self::open`] to
    /// access it. Also called the 'private' part of the invariant.
    /// - `public`: the 'public' part of the invariant.
    /// - `namespace`: the namespace of the invariant.
    ///   This is required to avoid [open](Self::open)ing the same invariant twice.
    #[trusted]
    #[requires(value.invariant_with_data(*public))]
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
    #[trusted]
    #[logic]
    pub fn namespace(self) -> Namespace {
        dead
    }

    /// Get the 'public' part of this invariant.
    #[trusted]
    #[logic]
    pub fn public(self) -> T::Public {
        dead
    }

    /// Open the invariant to get the data stored inside.
    ///
    /// This will call the closure `f` with the inner data. You must restore the
    /// contained [`LocalInvariantSpec`] before returning from the closure.
    #[trusted]
    #[requires(namespaces@.contains(this.namespace()))]
    #[requires(forall<t: Ghost<&mut T>> (**t).invariant_with_data(this.public()) && inv(t) ==>
        f.precondition((t,)) &&
        // f must restore the invariant
        (forall<res: A> f.postcondition_once((t,), res) ==> (^*t).invariant_with_data(this.public())))]
    #[ensures(exists<t: Ghost<&mut T>> (**t).invariant_with_data(this.public()) && f.postcondition_once((t,), result))]
    #[check(ghost)]
    pub fn open<'a, A>(
        this: Ghost<&'a Self>,
        namespaces: Ghost<Namespaces<'a>>,
        f: impl FnOnce(Ghost<&'a mut T>) -> A,
    ) -> A {
        let _ = namespaces;
        // SAFETY: this operation happens in a ghost block, meaning it only
        // make sense when compiling with creusot: in this case, Creusot will
        // make sure that this is in fact safe.
        let borrow = ghost!(unsafe { &mut *this.value.get() });
        f(borrow)
    }
}
