// WHY3SKIP

#![allow(creusot::contractless_external_function)]

use std::{
    sync::atomic::{AtomicI32, Ordering},
    thread,
};

use creusot_std::prelude::erasure;

#[erasure(spec::parallel_add)]
pub fn parallel_add() {
    let atomic = AtomicI32::new(0);

    thread::scope(|s| {
        s.spawn(|| {
            atomic.fetch_add(2, Ordering::Relaxed);
        });

        s.spawn(|| {
            atomic.fetch_add(2, Ordering::Relaxed);
        });
    });

    let n = atomic.into_inner();
    assert!(n == 4i32);
}

mod spec {
    include!("../rlx.rs");
}
