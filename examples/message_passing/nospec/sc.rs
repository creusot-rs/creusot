#![feature(sync_unsafe_cell)]

use std::{
    cell::SyncUnsafeCell,
    sync::atomic::{AtomicBool, Ordering},
    thread,
};

use creusot_std::prelude::erasure;

#[erasure(spec::message_passing)]
pub fn message_passing() {
    let atomic = AtomicBool::new(false);
    let data = SyncUnsafeCell::new(0);

    thread::scope(|s| {
        let data = &data;
        let atomic = &atomic;

        let t1 = s.spawn(move || {
            unsafe { *data.get() = 1 };
            atomic.store(true, Ordering::SeqCst);
        });

        let t2 = s.spawn(move || {
            while !atomic.load(Ordering::SeqCst) {}

            let res = unsafe { *data.get() };
            assert!(res == 1);
        });

        let _ = t1.join();
        let _ = t2.join();
    });
}

mod spec {
    include!("../sc.rs");
}
