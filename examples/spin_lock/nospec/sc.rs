// COMASKIP

#![feature(sync_unsafe_cell)]
#![allow(creusot::contractless_external_function)]

use std::{
    cell::SyncUnsafeCell,
    sync::atomic::{AtomicBool, Ordering},
};

use creusot_std::std::sync::SyncViewExt;

pub struct SpinLock<T> {
    flag: AtomicBool,
    data: SyncUnsafeCell<T>,
}

pub struct SpinLockGuard<'a, T> {
    lock: &'a SpinLock<T>,
}

impl<T> SpinLock<T> {
    pub fn new(data: T) -> Self {
        let data = SyncUnsafeCell::new(data);
        let flag = AtomicBool::new(false);

        SpinLock { flag, data }
    }

    pub fn lock<'a>(&'a self) -> SpinLockGuard<'a, T> {
        while let Err(_) =
            self.flag.compare_exchange_weak(false, true, Ordering::SeqCst, Ordering::SeqCst)
        {
        }

        SpinLockGuard { lock: self }
    }

    pub fn into_inner(self) -> T {
        self.data.into_inner()
    }
}

impl<'a, T> SpinLockGuard<'a, T> {
    pub fn deref(&self) -> &T {
        unsafe { self.lock.data.borrow() }
    }

    pub fn deref_mut(&mut self) -> &mut T {
        unsafe { self.lock.data.borrow_mut() }
    }

    pub fn unlock(self) {
        self.lock.flag.store(false, Ordering::SeqCst);
    }
}

pub mod spec {
    erase! {
        type SpinLock<T> => super::SpinLock<T>;
        type SpinLockGuard<T> => super::SpinLockGuard<'_, T>;
        fn SpinLock::<T>::new => super::SpinLock::<T>::new;
        fn SpinLock::<T>::lock => super::SpinLock::<T>::lock;
        fn SpinLock::<T>::into_inner => super::SpinLock::<T>::into_inner;
        fn SpinLockGuard::<T>::deref => super::SpinLockGuard::<T>::deref;
        fn SpinLockGuard::<T>::deref_mut => super::SpinLockGuard::<T>::deref_mut;
        fn SpinLockGuard::<T>::unlock => super::SpinLockGuard::<T>::unlock;
    }

    include!("../sc.rs");
}
