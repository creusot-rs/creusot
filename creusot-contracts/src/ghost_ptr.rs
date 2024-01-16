// Inspired by https://plv.mpi-sws.org/rustbelt/ghostcell/ https://rust-unofficial.github.io/too-many-lists/fifth.html
use crate::{logic::FMap, *};
use ::std::{
    marker::PhantomData,
    ops::{Deref, DerefMut},
};

/// Models a fragment of the heap that maps the [`GhostPtr`]s it has permission to their value.
/// At most one [`GhostToken`] has permission to each [`GhostPtr`]
/// No [`GhostToken`] has permission to a dangling [`GhostPtr`]
#[trusted]
pub struct GhostPtrToken<T: ?Sized>(PhantomData<T>);

/// ZST equivalent of [`&'a GhostPtrToken<T>`](GhostPtrToken)
/// Can be created using [`GhostPtrToken::borrow`]
#[trusted]
#[derive(Copy, Clone)]
pub struct GhostPtrTokenRef<'a, T: ?Sized>(PhantomData<&'a T>);

/// ZST equivalent of [`&'a mut GhostPtrToken<T>`](GhostPtrToken)
/// Can be created using [`GhostPtrToken::borrow_mut`]
#[trusted]
pub struct GhostPtrTokenMut<'a, T: ?Sized>(PhantomData<&'a mut T>);

/// Thin wrapper over a raw pointer managed by a [`GhostPtr`]
pub type GhostPtr<T> = *const T;

impl<T: ?Sized> ShallowModel for GhostPtrToken<T> {
    type ShallowModelTy = FMap<GhostPtr<T>, T>;

    #[trusted]
    #[ghost]
    #[open(self)]
    fn shallow_model(self) -> Self::ShallowModelTy {
        absurd
    }
}

impl<T: ?Sized> GhostPtrToken<T> {
    /// Creates a new [`GhostPtr`] that has no permission
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
    // Safety this pointer was owned by a box so no other GhostToken could have permission to it
    #[trusted]
    #[ensures(!(*self)@.contains(result))]
    // Since we had full permission to `val` and all of the entries in `self` simultaneously,
    // it couldn't have already been contained in `self`
    #[ensures((^self)@ == (*self)@.insert(result, *val))]
    pub fn ptr_from_box(&mut self, val: Box<T>) -> *const T {
        Box::into_raw(val)
    }

    /// Immutably borrows `ptr`
    // Safety no other token has permission to `ptr`
    // `t` cannot be used to mutably borrow `ptr` as long as the shared lifetime lasts
    #[trusted]
    #[requires(self@.contains(ptr))]
    #[ensures(*result == *self@.lookup_unsized(ptr))]
    pub fn ptr_as_ref(&self, ptr: *const T) -> &T {
        unsafe { &*ptr }
    }

    /// Mutably borrows `ptr`
    #[requires(self@.contains(ptr))]
    #[ensures(*result == *(*self)@.lookup_unsized(ptr))]
    #[ensures((^self)@ == (*self)@.insert(ptr, ^result))]
    pub fn ptr_as_mut(&mut self, ptr: *const T) -> &mut T {
        self.borrow_mut().take_mut(ptr)
    }

    /// Transfers ownership of `ptr` back into a `Box`
    // Safety `ptr` is now dangling but since `self` doesn't have permission anymore no token does so this is okay
    #[trusted]
    #[requires((*self)@.contains(ptr))]
    #[ensures(*result == *(*self)@.lookup_unsized(ptr))]
    #[ensures((^self)@ == (*self)@.remove(ptr))]
    pub fn ptr_to_box(&mut self, ptr: *const T) -> Box<T> {
        unsafe { Box::from_raw(ptr as *mut _) }
    }

    #[trusted]
    #[ensures((*self)@.disjoint(_other@))]
    // Since we had full permission to and all of the entries in `self` and `other` simultaneously,
    // no pointer could have been in both
    #[ensures((^self)@ == (*self)@.union(_other@))]
    pub fn merge(&mut self, _other: GhostPtrToken<T>) {}

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
    #[ensures(result.curr() == (*result)@)]
    #[ensures(result.fin() == (^result)@)]
    pub fn borrow_mut(&mut self) -> GhostPtrTokenMut<'_, T> {
        GhostPtrTokenMut(PhantomData)
    }
}

impl<T: ?Sized> GhostPtrExt<T> for GhostPtr<T> {
    #[trusted]
    #[open(self)]
    #[ghost]
    #[ensures(forall<t: GhostPtrToken<T>> !t@.contains(result))]
    // #[ensures(result.addr_logic() == 0@)]
    #[ensures(forall<ptr: GhostPtr<T>> ptr.addr_logic() == result.addr_logic() ==> ptr == result)]
    fn null_logic() -> Self {
        absurd
    }

    #[trusted]
    #[ghost]
    #[open(self)]
    fn addr_logic(self) -> Int {
        absurd
    }
}

impl<'a, T: ?Sized> ShallowModel for GhostPtrTokenRef<'a, T> {
    type ShallowModelTy = FMap<GhostPtr<T>, T>;

    #[trusted]
    #[ghost]
    #[open(self)]
    fn shallow_model(self) -> Self::ShallowModelTy {
        absurd
    }
}

impl<'a, T: ?Sized> Deref for GhostPtrTokenRef<'a, T> {
    type Target = GhostPtrToken<T>;

    #[trusted]
    #[ensures(result@ == self@)]
    fn deref(&self) -> &Self::Target {
        &GhostPtrToken(PhantomData)
    }
}

impl<'a, T: ?Sized> GhostPtrTokenRef<'a, T> {
    /// Shrinks the view of the `self` so that it's model is now new-model
    #[trusted]
    #[requires(_new_model.subset(self@))]
    #[ensures(result@ == *_new_model)]
    pub fn shrink_token_ref(self, _new_model: Ghost<FMap<*const T, T>>) -> Self {
        self
    }
}

impl<'a, T: ?Sized> GhostPtrTokenMut<'a, T> {
    #[trusted]
    #[ghost]
    #[open(self)]
    pub fn curr(self) -> FMap<GhostPtr<T>, T> {
        absurd
    }

    #[trusted]
    #[logic]
    #[open(self)]
    pub fn fin(self) -> FMap<GhostPtr<T>, T> {
        absurd
    }

    #[ensures(self.fin() == self.cur())]
    #[ensures(result@ == self.cur())]
    pub fn shr(self) -> GhostPtrTokenRef<'a, T> {
        GhostPtrTokenRef(PhantomData)
    }

    /// Mutably borrows `ptr` and shrinks `t` so that it can no longer be used to access `ptr`
    // Safety no other token has permission to `self`
    // `t` can no longer be used to access `ptr`
    #[trusted]
    #[requires((*self).curr().contains(ptr))]
    #[ensures(*result == *(*self).curr().lookup_unsized(ptr))]
    #[ensures((^self).curr() == (*self).curr().remove(ptr))]
    #[ensures((*self).fin() == (^self).fin().insert(ptr, ^result))]
    #[ensures(!(^self).fin().contains(ptr))]
    pub fn take_mut(&mut self, ptr: *const T) -> &'a mut T {
        unsafe { &mut *(ptr as *mut _) }
    }
}

impl<'a, T> Deref for GhostPtrTokenMut<'a, T> {
    type Target = GhostPtrToken<T>;

    #[trusted]
    #[ensures(result@ == self.curr())]
    fn deref(&self) -> &Self::Target {
        &GhostPtrToken(PhantomData)
    }
}

impl<'a, T> DerefMut for GhostPtrTokenMut<'a, T> {
    #[trusted]
    #[ensures((*result)@ == (*self).curr())]
    #[ensures((^self).curr() == (^result)@)]
    fn deref_mut(&mut self) -> &mut Self::Target {
        Box::leak(Box::new(GhostPtrToken(PhantomData)))
    }
}

#[trusted]
impl<'a, T> Resolve for GhostPtrTokenMut<'a, T> {
    #[logic]
    #[open]
    fn resolve(self) -> bool {
        self.curr() == self.fin()
    }
}

pub trait GhostPtrExt<T: ?Sized>: Sized {
    #[ghost]
    fn null_logic() -> Self;
    #[ghost]
    fn addr_logic(self) -> Int;
}

extern_spec! {
    impl<T> *const T {
        // Safety since addr_logic is uninterpreted this just claims ptr::addr is deterministic
        #[trusted]
        #[ensures(result@ == self.addr_logic())]
        fn addr(self) -> usize;

        /// Check if `self` was created with ptr::null()
        #[trusted]
        #[ensures(result == (self == GhostPtr::<T>::null_logic()))]
        fn is_null(self) -> bool;
    }

    mod std {
        mod ptr {
            /// Creates a null pointer that no GhostToken has permission to
            // Safety even though this pointer is dangling no GhostToken has permission to it so it's okay
            #[trusted]
            #[ensures(result == GhostPtr::<T>::null_logic())]
            fn null<T>() -> *const T
            where
                T: Sized;
        }
    }
}
