// WHY3SKIP

#![feature(sync_unsafe_cell)]
#![allow(creusot::contractless_external_function)]

use std::{
    cell::SyncUnsafeCell,
    sync::atomic::{AtomicU32, Ordering},
};

use creusot_std::{
    prelude::{erase, erasure},
    std::sync::SyncViewExt,
};

pub struct TicketLock<T> {
    next_ticket: AtomicU32,
    now_serving: AtomicU32,
    data: SyncUnsafeCell<T>,
}

pub struct TicketLockGuard<'a, T> {
    lock: &'a TicketLock<T>,
}

erase! {
    type spec::TicketLock<T> => TicketLock<T>;
    type spec::TicketLockGuard<T> => TicketLockGuard<'_, T>;
}

impl<T> TicketLock<T> {
    #[erasure(spec::TicketLock::<T>::new)]
    pub fn new(data: T) -> Self {
        let data = SyncUnsafeCell::new(data);

        let next_ticket = AtomicU32::new(0);
        let now_serving = AtomicU32::new(0);

        TicketLock { next_ticket, now_serving, data }
    }

    #[erasure(spec::TicketLock::<T>::lock)]
    pub fn lock<'a>(&'a self) -> TicketLockGuard<'a, T> {
        let ticket = self.next_ticket.fetch_add(1, Ordering::SeqCst);

        while self.now_serving.load(Ordering::SeqCst) != ticket {}

        TicketLockGuard { lock: self }
    }

    #[erasure(spec::TicketLock::<T>::into_inner)]
    pub fn into_inner(self) -> T {
        self.data.into_inner()
    }
}

impl<'a, T> TicketLockGuard<'a, T> {
    #[erasure(spec::TicketLockGuard::<T>::deref)]
    pub fn deref(&self) -> &T {
        unsafe { self.lock.data.borrow() }
    }

    #[erasure(spec::TicketLockGuard::<T>::deref_mut)]
    pub fn deref_mut(&mut self) -> &mut T {
        unsafe { self.lock.data.borrow_mut() }
    }

    #[erasure(spec::TicketLockGuard::<T>::unlock)]
    pub fn unlock(self) {
        let ticket = self.lock.now_serving.load(Ordering::SeqCst);
        self.lock.now_serving.store(ticket.wrapping_add(1), Ordering::SeqCst);
    }
}

pub mod spec {
    include!("../sc.rs");
}
