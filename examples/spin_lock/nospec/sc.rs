// WHY3SKIP

#![feature(sync_unsafe_cell)]
#![allow(creusot::contractless_external_function)]

use std::{
    cell::SyncUnsafeCell,
    sync::atomic::{AtomicBool, Ordering},
};

use creusot_std::{
    prelude::{erase, erasure},
    std::sync::SyncViewExt,
};

pub struct SpinLock<T> {
    flag: AtomicBool,
    data: SyncUnsafeCell<T>,
}

pub struct SpinLockGuard<'a, T> {
    lock: &'a SpinLock<T>,
}

erase! {
    type spec::SpinLock<T> => SpinLock<T>;
    type spec::SpinLockGuard<T> => SpinLockGuard<'_, T>;
}

impl<T> SpinLock<T> {
    #[erasure(spec::SpinLock::<T>::new)]
    pub fn new(data: T) -> Self {
        let data = SyncUnsafeCell::new(data);
        let flag = AtomicBool::new(false);

        SpinLock { flag, data }
    }

    #[erasure(spec::SpinLock::<T>::lock)]
    pub fn lock<'a>(&'a self) -> SpinLockGuard<'a, T> {
        while let Err(_) =
            self.flag.compare_exchange_weak(false, true, Ordering::SeqCst, Ordering::SeqCst)
        {
        }

        SpinLockGuard { lock: self }
    }

    #[erasure(spec::SpinLock::<T>::into_inner)]
    pub fn into_inner(self) -> T {
        self.data.into_inner()
    }
}

impl<'a, T> SpinLockGuard<'a, T> {
    #[erasure(spec::SpinLockGuard::<T>::deref)]
    pub fn deref(&self) -> &T {
        unsafe { self.lock.data.borrow() }
    }

    #[erasure(spec::SpinLockGuard::<T>::deref_mut)]
    pub fn deref_mut(&mut self) -> &mut T {
        unsafe { self.lock.data.borrow_mut() }
    }

    #[erasure(spec::SpinLockGuard::<T>::unlock)]
    pub fn unlock(self) {
        self.lock.flag.store(false, Ordering::SeqCst);
    }
}

pub mod spec {
    include!("../sc.rs");
}
