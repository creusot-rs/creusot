// WHY3SKIP

#![allow(creusot::contractless_external_function)]

use std::{
    sync::atomic::{AtomicI32, Ordering},
    thread,
};

use creusot_std::{prelude::erasure, std::thread::JoinHandleExt};

#[erasure(spec::parallel_add)]
pub fn parallel_add() {
    let atomic = AtomicI32::new(0);

    thread::scope(|s| {
        let t1 = s.spawn(|| {
            atomic.fetch_add(2, Ordering::SeqCst);
        });

        let t2 = s.spawn(|| {
            atomic.fetch_add(2, Ordering::SeqCst);
        });

        let _ = t1.join_unwrap();
        let _ = t2.join_unwrap();
    });

    let n = atomic.into_inner();
    assert!(n == 4i32);
}

mod spec {
    include!("../sc.rs");
}
