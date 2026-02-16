extern crate creusot_std;

use creusot_std::{
    cell::PermCell,
    ghost::{Committer, invariant::declare_namespace},
    prelude::*,
    std::{
        sync::atomic_relacq::AtomicI32,
        thread::{self, JoinHandleExt},
    },
};

declare_namespace! { SPINLOCK }

pub fn spinlock() {
    let (data, mut data_own) = PermCell::new(0i32);
    let (atomic, atomic_own) = AtomicI32::new(0);

    thread::scope(|s| {
        let data = &data;
        let data_own = &mut data_own;
        let atomic = &atomic;

        let t1 = s.spawn(move |_| {
            unsafe {
                *data.borrow_mut(ghost!(&mut **data_own)) = 1;
            }
            atomic.store(1, ghost! { |c: &mut Committer<_>| {}});
        });

        let t2 = s.spawn(move |_| {
            loop {
                let (res, _) = atomic.load(ghost! { |c: &mut Committer<_>| {}});
                if res == 1 {
                    break;
                }
            }
        });

        let _ = t1.join_unwrap();
        let _ = t2.join_unwrap();
    });

    let res = data.into_inner(data_own);
    proof_assert!(res == 42i32);
}
