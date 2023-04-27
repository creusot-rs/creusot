// Inspired by https://plv.mpi-sws.org/rustbelt/ghostcell/ https://rust-unofficial.github.io/too-many-lists/fifth.html
use crate::{logic::FMap, util::MakeSized, *};
use ::std::marker::PhantomData;

/// Models a fragment of the heap that maps the [`GhostPtr`]s it has permission to their value.
/// At most one [`GhostToken`] has permission to each [`GhostPtr`]
/// No [`GhostToken`] has permission to a dangling [`GhostPtr`]
pub struct GhostPtrToken<T: ?Sized>(Ghost<FMap<GhostPtr<T>, T>>, PhantomData<T>);

/// Thin wrapper over a raw pointer managed by a [`GhostPtr`]
pub type GhostPtr<T> = *const T;

impl<T: ?Sized> ShallowModel for GhostPtrToken<T> {
    type ShallowModelTy = FMap<GhostPtr<T>, T>;

    #[logic]
    fn shallow_model(self) -> Self::ShallowModelTy {
        *self.0
    }
}

impl<T: ?Sized> GhostPtrToken<T> {
    /// Creates a new [`GhostPtr`] that has no permission
    #[ensures(result@ == FMap::empty())]
    pub fn new() -> Self {
        GhostPtrToken(ghost!(FMap::empty()), PhantomData)
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

    /// Leaks memory iff the precondition fails
    #[requires(self@.is_empty())]
    pub fn drop(self) {}
}

impl<T: ?Sized> GhostPtrExt<T> for GhostPtr<T> {
    #[trusted]
    #[logic]
    #[ensures(forall<t: GhostPtrToken<T>> !t@.contains(result))]
    #[ensures(forall<ptr: GhostPtr<T>> ptr.addr_logic() == result.addr_logic() ==> ptr == result)]
    fn null_logic() -> Self {
        absurd
    }

    #[trusted]
    #[logic]
    fn addr_logic(self) -> Int {
        absurd
    }
}

pub trait GhostPtrExt<T: ?Sized>: Sized {
    #[logic]
    fn null_logic() -> Self;
    #[logic]
    fn addr_logic(self) -> Int;
}

extern_spec! {
    impl<T> *const T {
        // Safety since addr_logic is uninterpreted this just claims ptr::addr is deterministic
        #[trusted]
        #[ensures(result@ == self.addr_logic())]
        fn addr(self) -> usize;

        /// Check if `self` was created with [`GhostPtr::null`]
        #[trusted]
        #[ensures(result == (self == GhostPtr::<T>::null_logic()))]
        fn is_null(self) -> bool;
    }

    mod std {
        mod ptr {
            /// Creates a null [`GhostPtr`] that no GhostToken has permission to
            // Safety even though this pointer is dangling no GhostToken has permission to it so it's okay
            #[trusted]
            #[ensures(result == GhostPtr::<T>::null_logic())]
            fn null<T>() -> *const T
            where
                T: Sized;
        }
    }
}

// Coverts `val` into a [`GhostPtr`] and gives `t` permission to it
// Safety this pointer was owned by a box so no other GhostToken could have permission to it
#[trusted]
#[ensures(!(*t)@.contains(result))]
#[ensures((^t)@ == (*t)@.insert(result, *val))]
pub fn ptr_from_box<T>(val: Box<T>, t: &mut GhostPtrToken<T>) -> *const T {
    Box::into_raw(val)
}

/// Immutably borrows `self`
// Safety no other token has permission to `self`
// `t` cannot be used to mutably borrow `self` as long as the shared lifetime lasts
#[trusted]
#[requires(t@.contains(ptr))]
#[ensures(*result == t@.lookup(ptr))]
pub fn ptr_as_ref<T>(ptr: *const T, t: &GhostPtrToken<T>) -> &T {
    unsafe { &*ptr }
}

#[trusted]
#[requires(new_model.subset((*t)@))]
#[ensures((*result)@ == *new_model)]
pub fn shrink_token_ref<T>(
    t: &GhostPtrToken<T>,
    new_model: Ghost<<GhostPtrToken<T> as ShallowModel>::ShallowModelTy>,
) -> &GhostPtrToken<T> {
    t
}

/// Mutably borrows `ptr` and shrinks `t` so that it can no longer be used to access `ptr`
// Safety no other token has permission to `self`
// `t` can no longer be used to access `ptr`
#[trusted]
#[requires((**t)@.contains(ptr))]
#[ensures(*result == (**t)@.lookup(ptr))]
#[ensures((*^t)@ == (**t)@.remove(ptr))]
#[ensures((^*t)@.remove(ptr) == (^^t)@)]
#[ensures((^*t)@.get(ptr) == Some((^result).make_sized()))]
#[ensures(!(^^t)@.contains(ptr))]
pub fn ptr_as_mut2<'o, 'i, T>(ptr: *const T, t: &'o mut &'i mut GhostPtrToken<T>) -> &'i mut T {
    unsafe { &mut *(ptr as *mut _) }
}

#[requires(t@.contains(ptr))]
#[ensures(*result == (*t)@.lookup(ptr))]
#[ensures((^t)@ == (*t)@.insert(ptr, ^result))]
pub fn ptr_as_mut<T>(ptr: *const T, t: &mut GhostPtrToken<T>) -> &mut T {
    let mut t = t;
    ptr_as_mut2(ptr, &mut t)
}

// Deallocates `ptr` back into a `Box`
// Safety `ptr` is now dangling but since `t` doesn't have permission anymore no token does so this is okay
#[trusted]
#[requires((*t)@.contains(ptr))]
#[ensures(*result == (*t)@.lookup(ptr))]
#[ensures((^t)@ == (*t)@.remove(ptr))]
pub fn ptr_to_box<T>(ptr: *const T, t: &mut GhostPtrToken<T>) -> Box<T> {
    unsafe { Box::from_raw(ptr as *mut _) }
}

#[trusted]
#[ensures((*t)@.disjoint(other@))]
#[ensures((^t)@ == (*t)@.union(other@))]
pub fn merge<T>(t: &mut GhostPtrToken<T>, other: GhostPtrToken<T>) {}
