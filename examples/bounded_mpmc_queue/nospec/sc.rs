// RECURSION_LIMIT 256 COMASKIP

// This implementation is an adaption from:
// https://sites.google.com/site/1024cores/home/lock-free-algorithms/queues/bounded-mpmc-queue

#![feature(sync_unsafe_cell)]
#![allow(creusot::contractless_external_function)]

use core::mem::{MaybeUninit, replace};
use creusot_std::std::sync::SyncViewExt;
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

impl<T> Queue<T> {
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

    pub fn try_enqueue(&self, item: T) -> bool {
        let head = self.head.load(Ordering::SeqCst);
        let head_mod = head % self.cells.len();

        let cell = &self.cells[head_mod];
        let status = cell.status.load(Ordering::SeqCst);

        if 2 * head != status {
            return false;
        }

        let res =
            self.head.compare_exchange_weak(head, head + 1, Ordering::SeqCst, Ordering::SeqCst);

        if res.is_err() {
            return false;
        }

        unsafe { *cell.item.borrow_mut() = MaybeUninit::new(item) };

        cell.status.store(2 * head + 1, Ordering::SeqCst);

        true
    }

    pub fn try_dequeue(&self) -> Option<T> {
        let tail = self.tail.load(Ordering::SeqCst);
        let tail_mod = tail % self.cells.len();

        let cell = &self.cells[tail_mod];
        let status = cell.status.load(Ordering::SeqCst);

        if 2 * tail + 1 != status {
            return None;
        }

        let res =
            self.tail.compare_exchange_weak(tail, tail + 1, Ordering::SeqCst, Ordering::SeqCst);

        if res.is_err() {
            return None;
        }

        let item = unsafe { replace(cell.item.borrow_mut(), MaybeUninit::uninit()).assume_init() };

        cell.status.store(2 * (tail + self.cells.len()), Ordering::SeqCst);

        Some(item)
    }
}

pub mod spec {
    erase! {
        type Queue<T> => super::Queue<T>;
        type QueueCell<T> => super::QueueCell<T>;
        fn Queue::<T>::new => super::Queue::<T>::new;
        fn Queue::<T>::try_enqueue::<F> => super::Queue::<T>::try_enqueue where F: FnGhost + FnOnce(&mut QueueCommitter<T>);
        fn Queue::<T>::try_dequeue::<F> => super::Queue::<T>::try_dequeue where F: FnGhost + FnOnce(&mut QueueCommitter<T>);
    }

    include!("../sc.rs");
}
