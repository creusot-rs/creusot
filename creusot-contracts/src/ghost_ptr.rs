// Inspired by https://plv.mpi-sws.org/rustbelt/ghostcell/ https://rust-unofficial.github.io/too-many-lists/fifth.html
#[cfg(creusot)]
use crate::resolve::structural_resolve;
use crate::{invariant::*, logic::FMap, Clone, *};
use ::std::{
    marker::PhantomData,
    ops::{Deref, DerefMut},
};

/// Models a fragment of the heap that maps the [`GhostPtr`]s it has permission to their value.
/// At most one [`GhostPtrToken`] has permission to each [`GhostPtr`]
/// No [`GhostPtrToken`] has permission to a dangling [`GhostPtr`]
#[trusted]
pub struct GhostPtrToken<T: ?Sized>(PhantomData<T>);

/// ZST equivalent of [`&'a GhostPtrToken<T>`](GhostPtrToken)
/// Can be created using [`GhostPtrToken::borrow`]
#[trusted]
pub struct GhostPtrTokenRef<'a, T: ?Sized>(PhantomData<&'a T>);

/// ZST equivalent of [`&'a mut GhostPtrToken<T>`](GhostPtrToken)
/// Can be created using [`GhostPtrToken::borrow_mut`]
#[trusted]
pub struct GhostPtrTokenMut<'a, T: ?Sized>(PhantomData<&'a mut T>);

/// Thin wrapper over a raw pointer managed by a [`GhostPtr`]
pub type GhostPtr<T> = *const T;

impl<T: ?Sized> View for GhostPtrToken<T> {
    type ViewTy = FMap<GhostPtr<T>, T>;

    #[trusted]
    #[logic]
    #[ensures(result.get(GhostPtr::null_logic()) == None)]
    fn view(self) -> Self::ViewTy {
        dead
    }
}

impl<T: ?Sized> Invariant for GhostPtrToken<T> {
    #[predicate(prophetic)]
    #[open]
    #[creusot::trusted_ignore_structural_inv]
    #[creusot::trusted_is_tyinv_trivial_if_param_trivial]
    fn invariant(self) -> bool {
        pearlite! { forall<ptr: GhostPtr<T>, x: _> self@.get(ptr) == Some(x) ==> inv(*x) }
    }
}

impl<T: ?Sized> GhostPtrToken<T> {
    /// Creates a new [`GhostPtr`] that has no permission
    #[trusted]
    #[ensures(result@ == FMap::empty())]
    pub fn new() -> Self {
        GhostPtrToken(PhantomData)
    }

    #[trusted]
    #[ensures(forall<ptr1: GhostPtr<T>, ptr2: GhostPtr<T>>
        self@.contains(ptr1) && self@.contains(ptr2) && ptr1.addr_logic() == ptr2.addr_logic()
        ==> ptr1 == ptr2)]
    fn injective_lemma(&self) {}

    #[requires(self@.contains(ptr1) || ptr1 == GhostPtr::null_logic())]
    #[requires(self@.contains(ptr2) || ptr2 == GhostPtr::null_logic())]
    #[ensures(result == (ptr1.addr_logic() == ptr2.addr_logic()))]
    #[ensures(result == (ptr1 == ptr2))]
    pub fn are_eq(&self, ptr1: GhostPtr<T>, ptr2: GhostPtr<T>) -> bool
    where
        T: Sized,
    {
        self.injective_lemma();
        ptr1.addr() == ptr2.addr()
    }

    /// Casts `val` into a raw pointer and gives `self` permission to it
    // Safety this pointer was owned by a box so no other GhostPtrToken could have permission to it
    #[trusted]
    #[ensures(!(*self)@.contains(result))]
    // Since we had full permission to `val` and all of the entries in `self` simultaneously,
    // it couldn't have already been contained in `self`
    #[ensures((^self)@ == (*self)@.insert(result, *val))]
    pub fn ptr_from_box(&mut self, val: Box<T>) -> GhostPtr<T> {
        assert!(core::mem::size_of_val::<T>(&*val) > 0, "GhostPtrToken doesn't support ZSTs");
        Box::into_raw(val)
    }

    /// Immutably borrows `ptr`
    // Safety no other token has permission to `ptr`
    // `t` cannot be used to mutably borrow `ptr` as long as the shared lifetime lasts
    #[trusted]
    #[requires(self@.contains(ptr))]
    #[ensures(*result == *self@.lookup_unsized(ptr))]
    pub fn ptr_as_ref(&self, ptr: GhostPtr<T>) -> &T {
        unsafe { &*ptr }
    }

    /// Mutably borrows `ptr`
    #[requires(self@.contains(ptr))]
    #[ensures(*result == *(*self)@.lookup_unsized(ptr))]
    #[ensures((^self)@ == (*self)@.insert(ptr, ^result))]
    pub fn ptr_as_mut(&mut self, ptr: GhostPtr<T>) -> &mut T {
        self.borrow_mut().take_mut(ptr)
    }

    /// Transfers ownership of `ptr` back into a `Box`
    // Safety `ptr` is now dangling but since `self` doesn't have permission anymore no token does so this is okay
    #[trusted]
    #[requires((*self)@.contains(ptr))]
    #[ensures(*result == *(*self)@.lookup_unsized(ptr))]
    #[ensures((^self)@ == (*self)@.remove(ptr))]
    pub fn ptr_to_box(&mut self, ptr: GhostPtr<T>) -> Box<T> {
        unsafe { Box::from_raw(ptr as *mut _) }
    }

    #[trusted]
    #[ensures((*self)@.disjoint(other@))]
    // Since we had full permission to and all of the entries in `self` and `other` simultaneously,
    // no pointer could have been in both
    #[ensures((^self)@ == (*self)@.union(other@))]
    #[allow(unused_variables)]
    pub fn merge(&mut self, other: GhostPtrToken<T>) {}

    /// Leaks memory iff the precondition fails
    #[requires(self@.is_empty())]
    pub fn drop(self) {}

    /// Convert a shared reference in an equivalent ZST
    #[trusted]
    #[ensures(result@ == self@)]
    pub fn borrow(&self) -> GhostPtrTokenRef<'_, T> {
        GhostPtrTokenRef(PhantomData)
    }

    /// Convert a mutable reference in an equivalent ZST
    #[trusted]
    #[ensures(result.cur() == (*self)@)]
    #[ensures(result.fin() == (^self)@)]
    pub fn borrow_mut(&mut self) -> GhostPtrTokenMut<'_, T> {
        GhostPtrTokenMut(PhantomData)
    }
}

impl<T: ?Sized> GhostPtrExt<T> for GhostPtr<T> {
    #[trusted]
    #[logic]
    #[ensures(result.addr_logic() == 0)]
    #[ensures(forall<ptr: GhostPtr<T>> ptr.addr_logic() == result.addr_logic() ==> ptr == result)]
    fn null_logic() -> Self {
        dead
    }

    #[trusted]
    #[logic]
    fn addr_logic(self) -> Int {
        dead
    }
}

impl<'a, T: ?Sized> View for GhostPtrTokenRef<'a, T> {
    type ViewTy = FMap<GhostPtr<T>, T>;

    #[trusted]
    #[logic]
    #[ensures(result.get(GhostPtr::null_logic()) == None)]
    fn view(self) -> Self::ViewTy {
        dead
    }
}

impl<'a, T: ?Sized> Deref for GhostPtrTokenRef<'a, T> {
    type Target = GhostPtrToken<T>;

    #[ensures(result@ == self@)]
    fn deref(&self) -> &Self::Target {
        self.to_ref()
    }
}

impl<'a, T: ?Sized> GhostPtrTokenRef<'a, T> {
    /// Shrinks the view of the `self` so that it's model is now new-model
    #[trusted]
    #[requires(new_model.subset(self@))]
    #[ensures(result@ == *new_model)]
    #[allow(unused_variables)]
    pub fn shrink_token_ref(self, new_model: Snapshot<FMap<GhostPtr<T>, T>>) -> Self {
        self
    }

    #[trusted]
    #[ensures(result@ == self@)]
    pub fn to_ref(self) -> &'a GhostPtrToken<T> {
        &GhostPtrToken(PhantomData)
    }
}

impl<'a, T: ?Sized> Copy for GhostPtrTokenRef<'a, T> {}

impl<'a, T: ?Sized> Clone for GhostPtrTokenRef<'a, T> {
    #[ensures(result == *self)]
    fn clone(&self) -> Self {
        *self
    }
}

impl<'a, T: ?Sized> GhostPtrTokenMut<'a, T> {
    #[trusted]
    #[logic]
    #[ensures(result.get(GhostPtr::null_logic()) == None)]
    pub fn cur(self) -> FMap<GhostPtr<T>, T> {
        dead
    }

    #[trusted]
    #[logic(prophetic)]
    #[ensures(result.get(GhostPtr::null_logic()) == None)]
    pub fn fin(self) -> FMap<GhostPtr<T>, T> {
        dead
    }

    #[trusted]
    #[ensures(self.fin() == self.cur())]
    #[ensures(result@ == self.cur())]
    pub fn shr(self) -> GhostPtrTokenRef<'a, T> {
        GhostPtrTokenRef(PhantomData)
    }

    /// Mutably borrows `ptr` and shrinks `self` so that it can no longer be used to access `ptr`
    ///
    /// This function can be used to get multiple mutable references to non-aliasing pointers at the same time
    ///
    /// ```
    /// use creusot_contracts::ghost_ptr::GhostPtrToken;
    ///
    /// let mut token = GhostPtrToken::new();
    /// let ptr1 = token.ptr_from_box(Box::new(1));
    /// let ptr2 = token.ptr_from_box(Box::new(2));
    ///
    /// let mut token_mut = token.borrow_mut();
    /// let m1 = token_mut.take_mut(ptr1);
    /// // let m1_alias = token_mut.take_mut(ptr1); // Verification Error
    /// let m2 = token_mut.take_mut(ptr2);
    ///
    /// assert_eq!(*m1, 1);
    /// assert_eq!(*m2, 2);
    ///
    /// core::mem::swap(m1, m2);
    /// assert_eq!(*token.ptr_as_ref(ptr1), 2);
    /// assert_eq!(*token.ptr_as_ref(ptr2), 1);
    /// ```
    // Safety no other token has permission to `self`
    // `self` can no longer be used to access `ptr`
    #[trusted]
    #[requires((*self).cur().contains(ptr))]
    #[ensures(*result == *(*self).cur().lookup_unsized(ptr))]
    #[ensures((^self).cur() == (*self).cur().remove(ptr))]
    #[ensures((*self).fin() == (^self).fin().insert(ptr, ^result))]
    #[ensures(!(^self).fin().contains(ptr))]
    pub fn take_mut(&mut self, ptr: GhostPtr<T>) -> &'a mut T {
        unsafe { &mut *(ptr as *mut _) }
    }
}

impl<'a, T: ?Sized> Deref for GhostPtrTokenMut<'a, T> {
    type Target = GhostPtrToken<T>;

    #[trusted]
    #[ensures(result@ == self.cur())]
    fn deref(&self) -> &Self::Target {
        &GhostPtrToken(PhantomData)
    }
}

impl<'a, T: ?Sized> DerefMut for GhostPtrTokenMut<'a, T> {
    #[trusted]
    #[ensures((*result)@ == (*self).cur())]
    #[ensures((^self).cur() == (^result)@)]
    #[ensures((^self).fin() == (*self).fin())]
    fn deref_mut(&mut self) -> &mut Self::Target {
        Box::leak(Box::new(GhostPtrToken(PhantomData)))
    }
}

impl<'a, T: ?Sized> Resolve for GhostPtrTokenMut<'a, T> {
    #[open]
    #[predicate(prophetic)]
    fn resolve(self) -> bool {
        self.cur() == self.fin()
    }

    #[trusted]
    #[logic(prophetic)]
    #[open(self)]
    #[requires(structural_resolve(self))]
    #[ensures((*self).resolve())]
    fn resolve_coherence(&self) {}
}

pub trait GhostPtrExt<T: ?Sized>: Sized {
    #[logic]
    fn null_logic() -> Self;
    #[logic]
    fn addr_logic(self) -> Int;
}

extern_spec! {
    impl<T> GhostPtr<T> {
        // Safety since addr_logic is uninterpreted this just claims ptr::addr is deterministic
        #[ensures(result@ == self.addr_logic())]
        fn addr(self) -> usize;

        /// Check if `self` was created with ptr::null()
        #[ensures(result == (self == GhostPtr::<T>::null_logic()))]
        fn is_null(self) -> bool;
    }

    mod std {
        mod ptr {
            /// Creates a null pointer that no GhostPtrToken has permission to
            // Safety even though this pointer is dangling no GhostPtrToken has permission to it so it's okay
            #[ensures(result == GhostPtr::<T>::null_logic())]
            fn null<T>() -> GhostPtr<T>
            where
                T: std::ptr::Thin + ?Sized;
        }
    }
}
