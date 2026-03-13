use crate::{
    ghost::{Container, FnGhost, perm::Perm},
    prelude::*,
};
use core::marker::PhantomData;

macro_rules! impl_atomic {
    ($( ($type:ty, $atomic_type:ident) ),+) => { $(

        /// Creusot wrapper around [`std::sync::atomic::$atomic_type`]
        #[doc = concat!("Creusot wrapper around [`std::sync::atomic::", stringify!($atomic_type), "`].")]
        pub struct $atomic_type(::std::sync::atomic::$atomic_type);

        unsafe impl Send for Perm<$atomic_type> {}
        unsafe impl Sync for Perm<$atomic_type> {}

        impl Container for $atomic_type {
            type Value = $type;

            #[logic(open, inline)]
            fn is_disjoint(&self, _: &Self::Value, other: &Self, _: &Self::Value) -> bool {
                self != other
            }
        }

        impl $atomic_type {
            #[ensures(*result.1.val() == val)]
            #[ensures(*result.1.ward() == result.0)]
            #[trusted]
            #[check(terminates)]
            pub fn new(val: $type) -> (Self, Ghost<Box<Perm<$atomic_type>>>) {
                (Self(std::sync::atomic::$atomic_type::new(val)), Ghost::conjure())
            }

            #[doc = concat!("Wrapper for [`std::sync::atomic::", stringify!($atomic_type), "::into_inner`].")]
            #[requires(self == *own.ward())]
            #[ensures(result == *own.val())]
            #[trusted]
            #[allow(unused_variables)]
            pub fn into_inner(self, own: Ghost<Box<Perm<$atomic_type>>>) -> $type {
                self.0.into_inner()
            }

            #[doc = concat!("Wrapper for [`std::sync::atomic::", stringify!($atomic_type), "::load`].")]
            #[doc = ""]
            #[doc = "The load is always sequentially consistent."]
            #[requires(forall<c: &LoadCommitter<Self>> c.ward() == *self ==> f.precondition((c,)))]
            #[ensures(exists<c: &LoadCommitter<Self>>
                c.ward() == *self && c.val() == result && f.postcondition_once((c,), ())
            )]
            #[trusted]
            #[allow(unused_variables)]
            pub fn load<F>(&self, f: Ghost<F>) -> $type
            where
                F: FnGhost + FnOnce(&LoadCommitter<Self>),
            {
                self.0.load(std::sync::atomic::Ordering::SeqCst)
            }

            #[doc = concat!("Wrapper for [`std::sync::atomic::", stringify!($atomic_type), "::store`].")]
            #[doc = ""]
            #[doc = "The store is always sequentially consistent."]
            #[requires(forall<c: &mut StoreCommitter<Self>> !c.shot() ==> c.ward() == *self ==> c.val() == val ==>
                f.precondition((c,)) && f.postcondition_once((c,), ()) ==> (^c).shot()
            )]
            #[ensures(exists<c: &mut StoreCommitter<Self>>
                !c.shot() && c.ward() == *self && c.val() == val &&
                f.postcondition_once((c,), ())
            )]
            #[trusted]
            #[allow(unused_variables)]
            pub fn store<F>(&self, val: $type, f: Ghost<F>)
            where
                F: FnGhost + FnOnce(&mut StoreCommitter<Self>),
            {
                self.0.store(val, std::sync::atomic::Ordering::SeqCst)
            }
        }

    )* };
}

macro_rules! impl_atomic_int {
    ($( ($int_type:ty, $atomic_type:ident) ),+) => { $(

        impl_atomic!(($int_type, $atomic_type));

        impl $atomic_type {
            #[doc = concat!("Wrapper for [`std::sync::atomic::", stringify!($atomic_type), "::fetch_add`].")]
            #[doc = ""]
            #[doc = "The load and the store are always sequentially consistent."]
            #[requires(forall<c: &mut UpdateCommitter<Self>> !c.shot() ==> c.ward() == *self ==> c.new_val() == val + c.old_val() ==>
                f.precondition((c,)) && f.postcondition_once((c,), ()) ==> (^c).shot()
            )]
            #[ensures(exists<c: &mut UpdateCommitter<Self>>
                !c.shot() && c.ward() == *self && c.new_val() == val + c.old_val() &&
                c.old_val() == result && f.postcondition_once((c,), ())
            )]
            #[trusted]
            #[allow(unused_variables)]
            pub fn fetch_add<F>(&self, val: $int_type, f: Ghost<F>) -> $int_type
            where
                F: FnGhost + FnOnce(&mut UpdateCommitter<Self>),
            {
                self.0.fetch_add(val, std::sync::atomic::Ordering::SeqCst)
            }
        }

    )* };
}

impl_atomic! {
    (bool, AtomicBool)
}

impl_atomic_int! {
    (i8, AtomicI8),
    (u8, AtomicU8),
    (i16, AtomicI16),
    (u16, AtomicU16),
    (i32, AtomicI32),
    (u32, AtomicU32),
    (i64, AtomicI64),
    (u64, AtomicU64),
    (isize, AtomicIsize),
    (usize, AtomicUsize)
}

/// Wrapper around a single atomic load operation, where multiple ghost steps
/// can be performed.
///
/// Note: this committer has no observable effect on ghost ressources. Thus, it is optional to shoot
/// it, and nothing prevent the user from shooting it several times.
// This trick is correct for SC accesses under SC-DRF, and for Rel/Acq/Rlx and Rlx accesses, but
// perhaps not for C20's SC accesses.
#[opaque]
pub struct LoadCommitter<C: Container<Value: Sized>>(PhantomData<C>);

impl<C: Container<Value: Sized>> LoadCommitter<C> {
    /// Identity of the committer
    ///
    /// This is used so that we can only use the committer with the right [`AtomicOwn`].
    #[logic(opaque)]
    pub fn ward(self) -> C {
        dead
    }

    /// Value read from the atomic operation.
    #[logic(opaque)]
    pub fn val(self) -> C::Value {
        dead
    }

    /// 'Shoot' the committer
    ///
    /// This does the read on the atomic in ghost code, and can only be called once.
    #[requires(self.ward() == *(*own).ward())]
    #[ensures(self.val() == *own.val())]
    #[check(ghost)]
    #[trusted]
    #[allow(unused_variables)]
    pub fn shoot(&self, own: &Perm<C>) {
        panic!("Should not be called outside ghost code")
    }
}

/// Wrapper around a single atomic store operation, where multiple ghost steps
/// can be performed.
#[opaque]
pub struct StoreCommitter<C: Container<Value: Sized>>(PhantomData<C>);

impl<C: Container<Value: Sized>> StoreCommitter<C> {
    /// Status of the committer
    #[logic(opaque)]
    pub fn shot(self) -> bool {
        dead
    }

    /// Identity of the committer
    ///
    /// This is used so that we can only use the committer with the right [`AtomicOwn`].
    #[logic(opaque)]
    pub fn ward(self) -> C {
        dead
    }

    /// Value written by the atomic operation.
    #[logic(opaque)]
    pub fn val(self) -> C::Value {
        dead
    }

    /// 'Shoot' the committer
    ///
    /// This does the write on the atomic in ghost code, and can only be called once.
    #[requires(!(*self).shot())]
    #[requires(self.ward() == *(*own).ward())]
    #[ensures((^self).shot())]
    #[ensures((*self).ward() == (^self).ward() && (*self).val() == (^self).val())]
    #[ensures((*own).ward() == (^own).ward())]
    #[ensures(*(^own).val() == (*self).val())]
    #[check(ghost)]
    #[trusted]
    #[allow(unused_variables)]
    pub fn shoot(&mut self, own: &mut Perm<C>) {
        panic!("Should not be called outside ghost code")
    }
}

/// Wrapper around a single atomic update operation, where multiple ghost steps
/// can be performed.
#[opaque]
pub struct UpdateCommitter<C: Container<Value: Sized>>(PhantomData<C>);

impl<C: Container<Value: Sized>> UpdateCommitter<C> {
    /// Status of the committer
    #[logic(opaque)]
    pub fn shot(self) -> bool {
        dead
    }

    /// Identity of the committer
    ///
    /// This is used so that we can only use the committer with the right [`AtomicOwn`].
    #[logic(opaque)]
    pub fn ward(self) -> C {
        dead
    }

    /// Value held by the [`AtomicOwn`], before the [`shoot`].
    #[logic(opaque)]
    pub fn old_val(self) -> C::Value {
        dead
    }

    /// Value held by the [`AtomicOwn`], after the [`shoot`].
    #[logic(opaque)]
    pub fn new_val(self) -> C::Value {
        dead
    }

    /// 'Shoot' the committer
    ///
    /// This does the update on the atomic in ghost code, and can only be called once.
    #[requires(!(*self).shot())]
    #[requires(self.ward() == *(*own).ward())]
    #[ensures((^self).shot())]
    #[ensures((*self).ward() == (^self).ward())]
    #[ensures((*self).old_val() == (^self).old_val() && (*self).new_val() == (^self).new_val())]
    #[ensures((*own).ward() == (^own).ward())]
    #[ensures(*(*own).val() == (*self).old_val())]
    #[ensures(*(^own).val() == (*self).new_val())]
    #[check(ghost)]
    #[trusted]
    #[allow(unused_variables)]
    pub fn shoot(&mut self, own: &mut Perm<C>) {
        panic!("Should not be called outside ghost code")
    }
}
