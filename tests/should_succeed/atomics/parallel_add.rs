extern crate creusot_contracts;
use creusot_contracts::{
    ghost::atomic_invariant::{AtomicI32Own, Committer},
    prelude::*,
    std::thread,
};

pub fn parallel_add() {
    let (atomic, mut own) = AtomicI32Own::new(0);

    thread::scope(|s| {
        s.spawn(|_| {
            atomic.store(
                1,
                ghost! {
                    #[check(ghost)]
                    |c: &mut Committer| {
                        c.shoot(&mut *own);
                    }
                },
            );
        });

        // proof_assert!(own.val() == 1i32);
    });
}
