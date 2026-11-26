// COMASKIP

#![feature(sync_unsafe_cell)]
#![allow(creusot::contractless_external_function)]

use std::{
    cell::SyncUnsafeCell,
    sync::atomic::{AtomicU32, Ordering},
};

use creusot_std::std::sync::SyncViewExt;

pub struct TicketLock<T> {
    next_ticket: AtomicU32,
    now_serving: AtomicU32,
    data: SyncUnsafeCell<T>,
}

pub struct TicketLockGuard<'a, T> {
    lock: &'a TicketLock<T>,
}

impl<T> TicketLock<T> {
    pub fn new(data: T) -> Self {
        let data = SyncUnsafeCell::new(data);

        let next_ticket = AtomicU32::new(0);
        let now_serving = AtomicU32::new(0);

        TicketLock { next_ticket, now_serving, data }
    }

    pub fn lock<'a>(&'a self) -> TicketLockGuard<'a, T> {
        let ticket = self.next_ticket.fetch_add(1, Ordering::SeqCst);

        while self.now_serving.load(Ordering::SeqCst) != ticket {}

        TicketLockGuard { lock: self }
    }

    pub fn into_inner(self) -> T {
        self.data.into_inner()
    }
}

impl<'a, T> TicketLockGuard<'a, T> {
    pub fn deref(&self) -> &T {
        unsafe { self.lock.data.borrow() }
    }

    pub fn deref_mut(&mut self) -> &mut T {
        unsafe { self.lock.data.borrow_mut() }
    }

    pub fn unlock(self) {
        let ticket = self.lock.now_serving.load(Ordering::SeqCst);
        self.lock.now_serving.store(ticket.wrapping_add(1), Ordering::SeqCst);
    }
}

pub mod spec {
    erase! {
        type TicketLock<T> => super::TicketLock<T>;
        type TicketLockGuard<T> => super::TicketLockGuard<'_, T>;
        fn TicketLock::<T>::new => super::TicketLock::<T>::new;
        fn TicketLock::<T>::lock => super::TicketLock::<T>::lock;
        fn TicketLock::<T>::into_inner => super::TicketLock::<T>::into_inner;
        fn TicketLockGuard::<T>::deref => super::TicketLockGuard::<T>::deref;
        fn TicketLockGuard::<T>::deref_mut => super::TicketLockGuard::<T>::deref_mut;
        fn TicketLockGuard::<T>::unlock => super::TicketLockGuard::<T>::unlock;
    }

    include!("../sc.rs");
}
