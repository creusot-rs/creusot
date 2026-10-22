//! This implementation is an adaption from:
//! https://sites.google.com/site/1024cores/home/lock-free-algorithms/queues/bounded-mpmc-queue

#![feature(sync_unsafe_cell)]
#![allow(creusot::contractless_external_function)]
#![recursion_limit = "256"]

use core::mem::{MaybeUninit, replace};
use creusot_std::{
    ghost::ErasedGhostFn,
    prelude::{erase, erasure},
    std::sync::SyncViewExt,
};
use std::{
    cell::SyncUnsafeCell,
    sync::atomic::{AtomicUsize, Ordering},
};

pub struct Queue<T> {
    cells: Vec<QueueCell<T>>,
    head: AtomicUsize,
    tail: AtomicUsize,
}

struct QueueCell<T> {
    item: SyncUnsafeCell<MaybeUninit<T>>,
    status: AtomicUsize,
}

erase! {
    type spec::Queue<T> => Queue<T>;
    type spec::QueueCell<T> => QueueCell<T>;
}

impl<T: 'static> Queue<T> {
    #[erasure(spec::Queue::<T>::new)]
    pub fn new(length: usize) -> Self {
        let mut cells: Vec<QueueCell<T>> = Vec::new();

        for i in 0..length {
            let item = SyncUnsafeCell::new(MaybeUninit::uninit());
            let status = AtomicUsize::new(2 * i);

            cells.push(QueueCell { item, status })
        }

        let head = AtomicUsize::new(0);
        let tail = AtomicUsize::new(0);

        Queue { cells, head, tail }
    }

    #[erasure(spec::Queue::<T>::try_enqueue::<ErasedGhostFn<T, spec::ErasedQueue, ()>>)]
    pub fn try_enqueue(&self, item: T) -> bool {
        let head = self.head.load(Ordering::Relaxed);
        let head_mod = head % self.cells.len();

        let cell = &self.cells[head_mod];
        let status = cell.status.load(Ordering::Acquire);

        if 2 * head != status {
            return false;
        }

        let res =
            self.head.compare_exchange_weak(head, head + 1, Ordering::Relaxed, Ordering::Relaxed);

        if res.is_err() {
            return false;
        }

        unsafe { *cell.item.borrow_mut() = MaybeUninit::new(item) };

        cell.status.store(2 * head + 1, Ordering::Release);

        true
    }

    #[erasure(spec::Queue::<T>::try_dequeue::<ErasedGhostFn<T, spec::ErasedQueue, ()>>)]
    pub fn try_dequeue(&self) -> Option<T> {
        let tail = self.tail.load(Ordering::Relaxed);
        let tail_mod = tail % self.cells.len();

        let cell = &self.cells[tail_mod];
        let status = cell.status.load(Ordering::Acquire);

        if 2 * tail + 1 != status {
            return None;
        }

        let res =
            self.tail.compare_exchange_weak(tail, tail + 1, Ordering::Relaxed, Ordering::Relaxed);

        if res.is_err() {
            return None;
        }

        let item = unsafe { replace(cell.item.borrow_mut(), MaybeUninit::uninit()).assume_init() };

        cell.status.store(2 * (tail + self.cells.len()), Ordering::Release);

        Some(item)
    }
}

pub mod spec {
    include!("../relaxed.rs");

    pub struct ErasedQueue {}
    impl creusot_std::ghost::ErasedGhostFnArg for ErasedQueue {
        type Ty<'a, T: 'a> = QueueCommitter<'a, T>;
    }
}
