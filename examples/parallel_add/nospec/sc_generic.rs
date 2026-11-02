// WHY3SKIP

#![allow(creusot::contractless_external_function)]

use std::{
    sync::atomic::{AtomicI32, Ordering},
    thread,
    thread::ScopedJoinHandle,
};

use creusot_std::prelude::erasure;

#[erasure(spec::parallel_add)]
pub fn parallel_add(n: i32) {
    let atomic = AtomicI32::new(0);

    thread::scope(|s| {
        let mut handles: Vec<ScopedJoinHandle<_>> = vec![];

        for _ in 0..n {
            let h = s.spawn(|| {
                atomic.fetch_add(1, Ordering::SeqCst);
            });
            handles.push(h);
        }

        for h in handles {
            h.join().unwrap();
        }
    });

    let x = atomic.into_inner();
    assert!(n == x);
}

mod spec {
    include!("../sc_generic.rs");
}
