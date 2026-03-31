use crate::{
    ghost::{Container, FnGhost, perm::Perm},
    prelude::*,
    std::sync::{
        atomic::{Ordering, Ordering::Ordering as _},
        committer::Committer,
    },
};

macro_rules! impl_atomic {
    ($( ($type:ty, $atomic_type:ident $(< $T:ident >)?) ),+) => { $(

        /// Creusot wrapper around [`std::sync::atomic::$atomic_type`]
        #[doc = concat!("Creusot wrapper around [`std::sync::atomic::", stringify!($atomic_type), "`].")]
        pub struct $atomic_type $(< $T >)?(::std::sync::atomic::$atomic_type $(< $T >)?);

        unsafe impl $(< $T >)? Send for Perm<$atomic_type $(< $T >)?> {}
        unsafe impl $(< $T >)? Sync for Perm<$atomic_type $(< $T >)?> {}

        impl $(< $T >)? Container for $atomic_type $(< $T >)? {
            type Value = $type;

            #[logic(open, inline)]
            fn is_disjoint(&self, _: &Self::Value, other: &Self, _: &Self::Value) -> bool {
                self != other
            }
        }

        impl $(< $T >)? $atomic_type $(< $T >)? {
            #[ensures(*result.1.val() == val)]
            #[ensures(*result.1.ward() == result.0)]
            #[trusted]
            #[check(terminates)]
            pub fn new(val: $type) -> (Self, Ghost<Box<Perm<$atomic_type $(< $T >)?>>>) {
                (Self(::std::sync::atomic::$atomic_type::new(val)), Ghost::conjure())
            }

            #[doc = concat!("Wrapper for [`std::sync::atomic::", stringify!($atomic_type), "::into_inner`].")]
            #[requires(self == *own.ward())]
            #[ensures(result == *own.val())]
            #[trusted]
            #[allow(unused_variables)]
            pub fn into_inner(self, own: Ghost<Box<Perm<$atomic_type $(< $T >)?>>>) -> $type {
                self.0.into_inner()
            }

            #[doc = concat!("Wrapper for [`std::sync::atomic::", stringify!($atomic_type), "::load`].")]
            #[doc = ""]
            #[doc = "The load is always sequentially consistent."]
            #[requires(forall<c: &Committer<Self, $type, Ordering::SeqCst, Ordering::None>>
                c.ward() == *self ==> f.precondition((c,))
            )]
            #[ensures(exists<c: &Committer<Self, $type, Ordering::SeqCst, Ordering::None>>
                c.ward() == *self && c.val_load() == result && f.postcondition_once((c,), ())
            )]
            #[trusted]
            #[allow(unused_variables)]
            pub fn load<F>(&self, f: Ghost<F>) -> $type
            where
                F: FnGhost + FnOnce(&Committer<Self, $type, Ordering::SeqCst, Ordering::None>),
            {
                self.0.load(Ordering::SeqCst::ORDERING)
            }

            #[doc = concat!("Wrapper for [`std::sync::atomic::", stringify!($atomic_type), "::store`].")]
            #[doc = ""]
            #[doc = "The store is always sequentially consistent."]
            #[requires(forall<c: &mut Committer<Self, $type, Ordering::None, Ordering::SeqCst>>
                !c.shot_store() ==> c.ward() == *self ==> c.val_store() == val ==>
                f.precondition((c,)) && f.postcondition_once((c,), ()) ==> (^c).shot_store()
            )]
            #[ensures(exists<c: &mut Committer<Self, $type, Ordering::None, Ordering::SeqCst>>
                !c.shot_store() && c.ward() == *self && c.val_store() == val &&
                f.postcondition_once((c,), ())
            )]
            #[trusted]
            #[allow(unused_variables)]
            pub fn store<F>(&self, val: $type, f: Ghost<F>)
            where
                F: FnGhost + FnOnce(&mut Committer<Self, $type, Ordering::None, Ordering::SeqCst>),
            {
                self.0.store(val, Ordering::SeqCst::ORDERING)
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
            #[requires(forall<c: &mut Committer<Self, $int_type, Ordering::SeqCst, Ordering::SeqCst>>
                !c.shot_store() ==> c.ward() == *self ==> c.val_store() == val + c.val_load() ==>
                f.precondition((c,)) && f.postcondition_once((c,), ()) ==> (^c).shot_store()
            )]
            #[ensures(exists<c: &mut Committer<Self, $int_type, Ordering::SeqCst, Ordering::SeqCst>>
                !c.shot_store() && c.ward() == *self && c.val_store() == val + c.val_load() &&
                c.val_load() == result && f.postcondition_once((c,), ())
            )]
            #[trusted]
            #[allow(unused_variables)]
            pub fn fetch_add<F>(&self, val: $int_type, f: Ghost<F>) -> $int_type
            where
                F: FnGhost + FnOnce(&mut Committer<Self, $int_type, Ordering::SeqCst, Ordering::SeqCst>),
            {
                self.0.fetch_add(val, Ordering::SeqCst::ORDERING)
            }
        }

    )* };
}

impl_atomic! {
    (bool, AtomicBool),
    (*mut T, AtomicPtr<T>)
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
