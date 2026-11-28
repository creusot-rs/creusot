// COMASKIP

#![feature(sync_unsafe_cell)]
#![allow(creusot::contractless_external_function)]

use std::{
    sync::atomic::{AtomicBool, Ordering},
    thread,
};

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

pub mod spec {
    erase! {
        fn message_passing => super::message_passing;
    }

    include!("../rlx_options_simplest.rs");
}
