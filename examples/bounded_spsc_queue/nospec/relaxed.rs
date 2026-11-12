// WHY3SKIP

#![feature(sync_unsafe_cell)]
#![allow(creusot::contractless_external_function)]

use core::{
    cell::SyncUnsafeCell,
    mem::{MaybeUninit, replace},
    sync::atomic::{AtomicUsize, Ordering},
};

use creusot_std::{
    ghost::ErasedGhostFn,
    prelude::{erase, erasure},
    std::sync::SyncViewExt,
};

erase! {
    type spec::Queue<T> => Queue<T>;
    type spec::Producer<T> => Producer<T>;
    type spec::Consumer<T> => Consumer<T>;
}

pub struct Queue<T> {
    buffer: Vec<SyncUnsafeCell<MaybeUninit<T>>>,
    head: AtomicUsize,
    tail: AtomicUsize,
}

impl<T> Queue<T> {
    #[erasure(spec::Queue::<T>::new)]
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

impl<T: 'static> Producer<'_, T> {
    #[erasure(spec::Producer::<T>::enqueue::<ErasedGhostFn<T, spec::ErasedCommitter, ()>>)]
    pub fn enqueue(&mut self, item: T) {
        let queue = self.queue;
        let buffer_size = queue.buffer.len();

        let next = if self.head + 1 == buffer_size { 0 } else { self.head + 1 };

        loop {
            let tail = queue.tail.load(Ordering::Acquire);

            if tail != next {
                unsafe { *queue.buffer[self.head].borrow_mut() = MaybeUninit::new(item) };

                queue.head.store(next, Ordering::Release);
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

impl<T: 'static> Consumer<'_, T> {
    #[erasure(spec::Consumer::<T>::dequeue::<ErasedGhostFn<T, spec::ErasedCommitter, ()>>)]
    pub fn dequeue<F>(&mut self) -> T {
        let queue = self.queue;
        let buffer_size = queue.buffer.len();

        let next = if self.tail + 1 == buffer_size { 0 } else { self.tail + 1 };

        loop {
            let head = queue.head.load(Ordering::Acquire);

            if head != self.tail {
                let item = unsafe {
                    replace(queue.buffer[self.tail].borrow_mut(), MaybeUninit::uninit())
                        .assume_init()
                };

                queue.tail.store(next, Ordering::Release);
                self.tail = next;
                return item;
            }
        }
    }
}

#[erasure(spec::channel::<T>)]
pub fn channel<'a, T>(queue: &'a Queue<T>) -> (Producer<'a, T>, Consumer<'a, T>) {
    let prod = Producer { queue, head: 0 };
    let cons = Consumer { queue, tail: 0 };
    (prod, cons)
}

pub mod spec {
    include!("../relaxed.rs");

    pub struct ErasedCommitter {}
    impl creusot_std::ghost::ErasedGhostFnArg for ErasedCommitter {
        type Ty<'a, T: 'a> = QueueCommitter<'a, T>;
    }
}
