//! Generic permissions for accessing memory pointed to by pointers or within an interior mutable
//! type.

use crate::prelude::*;
#[cfg(creusot)]
use crate::resolve::structural_resolve;

pub trait PermTarget {
    type Value<'a>
    where
        Self: 'a;
    type PermPayload: ?Sized;

    #[logic(open, inline)]
    fn is_disjoint(
        &self,
        _self_val: Self::Value<'_>,
        other: &Self,
        _other_val: Self::Value<'_>,
    ) -> bool {
        self != other
    }
}

/// Token that represents the ownership of the contents of a container object. The container is
/// either an interior mutable type (e.g., `Perm` or atomic types) or a raw pointer.
///
/// A `Perm` only exists in the ghost world, and it must be used in conjunction with its container
/// in order to read or write the value.
///
/// Permissions are made unsized to guarantee that they cannot be replaced in a mutable reference.
/// This would allow the permission to outlive the reference it has been placed in. This makes it
/// easier to specify splitting a mutable reference of a permission to a slice, and makes it
/// possible to specify functions such as [`Perm::from_mut`].
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
///
/// ## Layout facts
///
/// Certain facts about the layout and alignment of pointers can be made available
/// through the type invariant of [`crate::std::ptr::PtrLive`] by calling [`Perm::live`].
#[opaque]
pub struct Perm<C: ?Sized + PermTarget>(#[allow(unused)] C::PermPayload);

impl<C: ?Sized + PermTarget> Perm<C> {
    /// Returns the underlying container that is managed by this permission.
    #[logic(opaque)]
    pub fn ward<'a>(self) -> &'a C {
        dead
    }

    /// Get the logical value contained by the container.
    #[logic(opaque)]
    pub fn val<'a>(self) -> C::Value<'a> {
        dead
    }

    /// If two permissions have different values, then they must be disjoint.
    ///
    /// This is a ghost lemma: calling it has no operational effects, but allows
    /// Creusot to deduce things based on the ownership of the arguments.
    ///
    /// Note that disjointness is defined with the `is_disjoint` logical
    /// function. In particular, pointers to ZST are always disjoint, and may
    /// indeed have different pointed-to values (for example, [`Snapshot`] or
    /// [`Ghost`] values).
    ///
    /// If you have a mutable borrow to one of the permissions, you should use
    /// [`Self::disjoint_lemma`] instead.
    ///
    /// This lemma can also be used the other way: if you have two pointer
    /// permissions (with non-ZST values) with the same ward, then their values
    /// are equal.
    ///
    /// # Example
    ///
    /// ```rust,creusot
    /// use creusot_std::prelude::*;
    /// use creusot_std::ghost::perm::Perm;
    ///
    /// #[requires(*perm1.ward() == p1 && *perm2.ward() == p2)]
    /// fn foo(
    ///     (p1, perm1): (*const i32, Ghost<&Perm<*const i32>>),
    ///     (p2, perm2): (*const i32, Ghost<&Perm<*const i32>>)) {
    ///     if p1 == p2 {
    ///         let v1 = *unsafe { Perm::as_ref(p1, perm1) };
    ///         let v2 = *unsafe { Perm::as_ref(p1, perm2) };
    ///         // If both pointers are equal, it does not matter which permission
    ///         // we read the value from
    ///         ghost! { perm1.disjoint_lemma_shared(*perm2) };
    ///         assert!(v1 == v2);
    ///     }
    /// }
    /// ```
    #[trusted]
    #[check(ghost)]
    #[ensures(self.val() != other.val() ==> self.ward().is_disjoint(self.val(), other.ward(), other.val()))]
    #[allow(unused_variables)]
    pub fn disjoint_lemma_shared(&self, other: &Self) {}

    /// If one owns two permissions in ghost code, then they correspond to different containers.
    #[trusted]
    #[check(ghost)]
    #[ensures(self.ward().is_disjoint(self.val(), other.ward(), other.val()))]
    #[ensures(*self == ^self)]
    #[allow(unused_variables)]
    pub fn disjoint_lemma(&mut self, other: &Self) {}
}

impl<C: ?Sized + PermTarget> Resolve for Perm<C> {
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
