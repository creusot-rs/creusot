//! Generic permissions for accessing memory pointed to by pointers or within an interior mutable
//! type.

use crate::prelude::*;
#[cfg(creusot)]
use crate::resolve::structural_resolve;
use std::marker::PhantomData;

pub trait Container {
    type Value: ?Sized;

    #[logic]
    fn is_disjoint(&self, self_val: &Self::Value, other: &Self, other_val: &Self::Value) -> bool;
}

/// Token that represents the ownership of the contents of a container object. The container is
/// either an interrior mutable type (e.g., `Perm` or atomic types) or a raw pointer.
///
/// A `Perm` only exists in the ghost world, and it must be used in conjunction with its container
/// in order to read or write the value.
///
/// Permissions are made unsized to guarantee that they cannot be replaced in a mutable reference.
/// This would allow the permission to outlive the reference it has been placed in. This makes it
/// easier to specify splitting a mutable reference of a permission to a slice, and makes it
/// possible to specify functions such as `Perm::from_mut`
///
/// # Pointer permissions
///
/// A particular case of permissions is the case of permissions for raw pointers (i.e., `C` is
/// `*const T`). In this case, the permission represents the ownership of the memory cell.
///
/// A warning regarding memory leaks: dropping a `Perm<*const T>` cannot deallocate the memory
/// corresponding to the pointer because it is a ghost value. One must thus remember to explicitly
/// call [`drop`] in order to free the memory tracked by a `Perm<*const T>` token.
///
/// ## Safety
///
/// When using Creusot to verify the code, all methods should be safe to call. Indeed,
/// Creusot ensures that every operation on the inner value uses the right [`Perm`] object
/// created by [`Perm::new`], ensuring safety in a manner similar to [ghost_cell](https://docs.rs/ghost-cell/latest/ghost_cell/).
///
/// ## `#[check(terminates)]`
///
/// `Perm<*const T>` methods, particularly constructors (`new`, `from_box`, `from_ref`, `from_mut`),
/// are marked `check(terminates)` rather than `check(ghost)` to prevent two things from happening
/// in ghost code:
/// 1. running out of pointer addresses;
/// 2. allocating too large objects.
///
/// Note that we already can't guard against these issues in program code.
/// But preventing them in ghost code is even more imperative to ensure soundness.
///
/// Specifically, creating too many pointers contradicts the [`Perm::disjoint_lemma`],
/// and allocating too large objects contradicts the [`Perm::invariant`] that
/// allocations have size at most `isize::MAX`.
#[opaque]
pub struct Perm<C: ?Sized + Container>(#[allow(unused)] [PhantomData<C::Value>]);

impl<C: ?Sized + Container> Perm<C> {
    /// Returns the underlying container that is managed by this permission.
    #[logic(opaque)]
    pub fn ward<'a>(self) -> &'a C {
        dead
    }

    /// Get the logical value contained by the container.
    #[logic(opaque)]
    pub fn val<'a>(self) -> &'a C::Value {
        dead
    }

    /// If one owns two permissions in ghost code, then they correspond to different containers.
    #[trusted]
    #[check(ghost)]
    #[ensures(self.ward().is_disjoint(self.val(), other.ward(), other.val()))]
    #[ensures(*self == ^self)]
    #[allow(unused_variables)]
    pub fn disjoint_lemma(&mut self, other: &Self) {}
}

impl<C: ?Sized + Container> Resolve for Perm<C> {
    #[logic(open, prophetic, inline)]
    #[creusot::trusted_trivial_if_param_trivial]
    fn resolve(self) -> bool {
        resolve(self.val())
    }

    #[trusted]
    #[logic(prophetic)]
    #[requires(inv(self))]
    #[requires(structural_resolve(self))]
    #[ensures(self.resolve())]
    fn resolve_coherence(self) {}
}

impl<C: ?Sized + Container<Value: Sized>> View for Perm<C> {
    type ViewTy = C::Value;

    #[logic(open, inline)]
    fn view(self) -> Self::ViewTy {
        *self.val()
    }
}
