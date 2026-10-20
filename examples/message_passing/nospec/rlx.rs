// WHY3SKIP

#![feature(sync_unsafe_cell)]
#![allow(creusot::contractless_external_function)]

use std::{
    cell::SyncUnsafeCell,
    sync::atomic::{AtomicBool, Ordering, fence},
    thread,
};

use creusot_std::{prelude::erasure, std::sync::SyncViewExt};

#[erasure(spec::message_passing)]
pub fn message_passing() {
    let flag = AtomicBool::new(false);
    let data = SyncUnsafeCell::new(0i32);

    thread::scope(|s| {
        s.spawn(|| {
            unsafe { *data.borrow_mut() = 42 };
            fence(Ordering::Release);
            flag.store(true, Ordering::Relaxed);
        });

        s.spawn(|| {
            while !flag.load(Ordering::Relaxed) {}
            fence(Ordering::Acquire);

            let res = unsafe { *data.borrow_mut() };
            assert!(res == 42);
        });
    });
}

mod spec {
    include!("../rlx.rs");
}
