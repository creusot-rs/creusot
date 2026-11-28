// COMASKIP

#![feature(sync_unsafe_cell)]
#![allow(creusot::contractless_external_function)]

use core::{
    cell::SyncUnsafeCell,
    mem::{MaybeUninit, replace},
    sync::atomic::{AtomicUsize, Ordering},
};

use creusot_std::std::sync::SyncViewExt;

pub struct Queue<T> {
    buffer: Vec<SyncUnsafeCell<MaybeUninit<T>>>,
    head: AtomicUsize,
    tail: AtomicUsize,
}

impl<T> Queue<T> {
    pub fn new(len: usize) -> Self {
        let mut buffer: Vec<SyncUnsafeCell<MaybeUninit<T>>> = Vec::new();

        for _ in 0..len {
            let cell = SyncUnsafeCell::new(MaybeUninit::uninit());
            buffer.push(cell);
        }

        let head = AtomicUsize::new(0);
        let tail = AtomicUsize::new(0);

        Queue { buffer, head, tail }
    }
}

pub struct Producer<'a, T> {
    queue: &'a Queue<T>,
    head: usize,
}

impl<T> Producer<'_, T> {
    pub fn enqueue(&mut self, item: T) {
        let queue = self.queue;
        let buffer_size = queue.buffer.len();

        let next = if self.head + 1 == buffer_size { 0 } else { self.head + 1 };

        loop {
            let tail = queue.tail.load(Ordering::SeqCst);

            if tail != next {
                unsafe { *queue.buffer[self.head].borrow_mut() = MaybeUninit::new(item) };

                queue.head.store(next, Ordering::SeqCst);
                self.head = next;
                return;
            }
        }
    }
}

pub struct Consumer<'a, T> {
    queue: &'a Queue<T>,
    tail: usize,
}

impl<T> Consumer<'_, T> {
    pub fn dequeue<F>(&mut self) -> T {
        let queue = self.queue;
        let buffer_size = queue.buffer.len();

        let next = if self.tail + 1 == buffer_size { 0 } else { self.tail + 1 };

        loop {
            let head = queue.head.load(Ordering::SeqCst);

            if head != self.tail {
                let item = unsafe {
                    replace(queue.buffer[self.tail].borrow_mut(), MaybeUninit::uninit())
                        .assume_init()
                };

                queue.tail.store(next, Ordering::SeqCst);
                self.tail = next;
                return item;
            }
        }
    }
}

pub fn channel<'a, T>(queue: &'a Queue<T>) -> (Producer<'a, T>, Consumer<'a, T>) {
    let prod = Producer { queue, head: 0 };
    let cons = Consumer { queue, tail: 0 };
    (prod, cons)
}

pub mod spec {
    erase! {
        type Queue<T> => super::Queue<T>;
        type Producer<T> => super::Producer<T>;
        type Consumer<T> => super::Consumer<T>;
        fn Queue::<T>::new => super::Queue::<T>::new;
        fn Producer::<T>::enqueue::<F> => super::Producer::<T>::enqueue where F: FnGhost + FnOnce(&mut QueueCommitter<T>);
        fn Consumer::<T>::dequeue::<F> => super::Consumer::<T>::dequeue::<F> where F: FnGhost + FnOnce(&mut QueueCommitter<T>);
        fn channel::<T> => super::channel::<T>;
    }

    include!("../sc.rs");
}
