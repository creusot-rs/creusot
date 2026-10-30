// WHY3SKIP

#![feature(sync_unsafe_cell)]
#![allow(creusot::contractless_external_function)]

use std::{
    sync::atomic::{AtomicBool, Ordering},
    thread,
};

use creusot_std::prelude::erasure;

#[erasure(spec::message_passing)]
pub fn message_passing() {
    let flag = AtomicBool::new(false);

    thread::scope(|s| {
        s.spawn(|| {
            flag.store(true, Ordering::Relaxed);
        });

        s.spawn(|| {
            while !flag.load(Ordering::Relaxed) {}

            let res = flag.load(Ordering::Relaxed);
            assert!(res == true);
        });
    });
}

mod spec {
    include!("../rlx_options_simplest.rs");
}
