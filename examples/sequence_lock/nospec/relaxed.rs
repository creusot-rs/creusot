// WHY3SKIP

#![feature(sync_unsafe_cell)]
#![allow(creusot::contractless_external_function)]

use core::sync::atomic::{AtomicU32, AtomicUsize, Ordering, fence};

use creusot_std::{
    ghost::ErasedGhostFn,
    prelude::{erase, erasure},
};

erase! {
    type spec::SeqLock => SeqLock;
    type spec::SeqLockGuard => SeqLockGuard;
}

pub struct SeqLock {
    seq: AtomicUsize,
    data0: AtomicU32,
    data1: AtomicU32,
}

impl SeqLock {
    #[erasure(spec::SeqLock::new)]
    pub fn new(val0: u32, val1: u32) -> Self {
        let data0 = AtomicU32::new(val0);
        let data1 = AtomicU32::new(val1);
        let seq = AtomicUsize::new(0);

        SeqLock { seq, data0, data1 }
    }

    // TODO: #[erasure(spec::SeqLock::read::<ErasedGhostFn<(), spec::ErasedCommitter, ()>>)]
    pub fn read(&self) -> (u32, u32) {
        loop {
            let seq1 = self.seq.load(Ordering::Acquire);

            if seq1 % 2 != 0 {
                continue;
            }

            let result0 = self.data0.load(Ordering::Relaxed);
            let result1 = self.data1.load(Ordering::Relaxed);

            fence(Ordering::Acquire);

            let seq2 = self.seq.load(Ordering::Relaxed);

            if seq1 == seq2 {
                return (result0, result1);
            }
        }
    }

    // TODO: #[erasure(spec::SeqLock::lock_write::<ErasedGhostFn<(), spec::ErasedCommitter, ()>>)]
    pub fn lock_write(&self) -> SeqLockGuard<'_> {
        loop {
            let seq = self.seq.load(Ordering::Relaxed);

            if seq % 2 != 0 {
                continue;
            }

            let next_seq = seq + 1;
            let res =
                self.seq.compare_exchange(seq, next_seq, Ordering::Acquire, Ordering::Relaxed);

            if res.is_err() {
                continue;
            }

            fence(Ordering::Release);

            return SeqLockGuard { seqlock: self, seq: next_seq };
        }
    }

    // TODO: #[erasure(spec::SeqLock::into_inner)]
    pub fn into_inner(self) -> (u32, u32) {
        let lock = self.lock_write();
        lock.read()
    }
}

pub struct SeqLockGuard<'a> {
    seqlock: &'a SeqLock,
    seq: usize,
}

impl SeqLockGuard<'_> {
    #[erasure(spec::SeqLockGuard::read)]
    pub fn read(&self) -> (u32, u32) {
        let ret0 = self.seqlock.data0.load(Ordering::Relaxed);
        let ret1 = self.seqlock.data1.load(Ordering::Relaxed);

        (ret0, ret1)
    }

    #[erasure(spec::SeqLockGuard::write)]
    pub fn write(&mut self, val0: u32, val1: u32) {
        self.seqlock.data0.store(val0, Ordering::Relaxed);
        self.seqlock.data1.store(val1, Ordering::Relaxed);
    }

    #[erasure(spec::SeqLockGuard::unlock::<ErasedGhostFn<(), spec::ErasedCommitter, ()>>)]
    pub fn unlock(self) {
        let next_seq = self.seq + 1;
        let SeqLockGuard { seqlock, .. } = self;

        seqlock.seq.store(next_seq, Ordering::Release);
    }
}

pub mod spec {
    include!("../relaxed.rs");

    pub struct ErasedCommitter {}
    impl creusot_std::ghost::ErasedGhostFnArg for ErasedCommitter {
        type Ty<'a, T: 'a> = SeqLockCommitter<'a>;
    }
}
