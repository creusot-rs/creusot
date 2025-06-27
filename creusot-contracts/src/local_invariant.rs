//! Define local invariants
//!
//! [Local invariants](LocalInvariant) are not the same as [invariants](Invariant): they
//! allow the use of a shared piece of data to be used in the invariant (see
//! [`LocalInvariantSpec`]), but in return they impose a much more restricted access to
//! the underlying data, as well as the use of [`Namespaces`].

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

/// The type of _namespaces_ associated with invariants.
///
/// Can be declared with the [`declare_namespace`] macro, and then attached to a local
/// invariant when creating it with [`LocalInvariant::new`].
#[cfg_attr(creusot, rustc_diagnostic_item = "namespace_ty")]
pub struct Namespace(());

impl Namespace {
    /// Used by [`declare_namespace`].
    #[logic]
    #[open(self)]
    #[requires(false)]
    #[doc(hidden)]
    pub fn new() -> Self {
        Self(())
    }
}

/// A collection of namespaces.
///
/// This is given at the start of the program, and must be passed along to [LocalInvariant::open].
pub struct Namespaces<'a>(::std::marker::PhantomData<&'a mut Vec<Namespace>>);

impl Namespaces<'_> {
    /// Get the underlying set of namespaces.
    ///
    /// Also accessible via the [`view`](View::view) (`@`) operator.
    #[logic]
    #[open(self)]
    #[trusted]
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
    #[ensures((*self).namespaces() == result.namespaces())]
    #[ensures((^self).namespaces() == result.namespaces())]
    #[trusted]
    #[pure]
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

pub struct LocalInvariant<T: LocalInvariantSpec> {
    value: UnsafeCell<T>,
    #[cfg_attr(not(creusot), allow(unused))]
    public: Snapshot<T::Public>,
    #[cfg_attr(not(creusot), allow(unused))]
    namespace: Snapshot<Namespace>,
}

/// A variant of [`Invariant`] for use in [`LocalInvariant`]s.
///
/// This allows to specify an invariant that depends on some [public data](LocalInvariant::public).
pub trait LocalInvariantSpec {
    type Public;

    #[logic(prophetic)]
    fn invariant_with_data(self, data: Self::Public) -> bool;
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
    #[requires(value.invariant_with_data(*public))]
    #[ensures(result.public() == *public)]
    #[ensures(result.namespace() == *namespace)]
    #[trusted]
    #[pure]
    pub fn new(
        value: Ghost<T>,
        public: Snapshot<T::Public>,
        namespace: Snapshot<Namespace>,
    ) -> Ghost<Self> {
        ghost!(Self { value: UnsafeCell::new(value.into_inner()), public, namespace })
    }

    /// Get the namespace associated with this invariant.
    #[logic]
    #[open(self)]
    pub fn namespace(self) -> Namespace {
        *self.namespace
    }

    /// Get the 'public' part of this invariant.
    #[logic]
    #[open(self)]
    pub fn public(self) -> T::Public {
        *self.public
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
        (forall<res: A> f.postcondition_once((t,), res) ==> (^t.inner_logic()).invariant_with_data(this.public())))]
    #[ensures(exists<t: Ghost<&mut T>> (**t).invariant_with_data(this.public()) && f.postcondition_once((t,), result))]
    #[pure]
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
