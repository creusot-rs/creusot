use core::sync::atomic::Ordering;

use creusot_std::{
    ghost::{
        invariant::{AtomicInvariantSC, Protocol, Tokens, declare_namespace},
        perm::Perm,
        resource::{Authority, Fragment},
    },
    logic::{Id, ra::excl::Excl},
    prelude::*,
    std::{
        sync::{
            atomic_sc::{AtomicI32, ordering::SeqCst},
            committer::Committer,
        },
        thread::{self, JoinHandleExt},
    },
};

declare_namespace! { PARALLEL_ADD }

type UpdateCommitter = Committer<AtomicI32, i32, SeqCst, SeqCst>;

struct PAInv {
    perm: Perm<AtomicI32>,
    auth1: Authority<Option<Excl<bool>>>,
    auth2: Authority<Option<Excl<bool>>>,
}

impl Protocol for PAInv {
    type Public = (AtomicI32, Id, Id);

    #[logic]
    fn public(self) -> Self::Public {
        (*self.perm.ward(), self.auth1.id(), self.auth2.id())
    }

    #[logic(inline)]
    fn protocol(self) -> bool {
        pearlite! {
            self.perm.val()@ ==
                if self.auth1@ == Some(Excl(true)) { 2 } else { 0 } +
                if self.auth2@ == Some(Excl(true)) { 2 } else { 0 }
        }
    }
}

pub fn parallel_add() {
    let (atomic, perm) = AtomicI32::new(0);

    let mut auth1 = ghost!(Authority::alloc().into_inner());
    let mut auth2 = ghost!(Authority::alloc().into_inner());
    let mut frag1 = ghost!(Fragment::new_unit(auth1.id()));
    let mut frag2 = ghost!(Fragment::new_unit(auth2.id()));
    ghost! {
        auth1.update(&mut frag1, snapshot!((Some(Excl(false)), Some(Excl(false)))));
        auth2.update(&mut frag2, snapshot!((Some(Excl(false)), Some(Excl(false)))));
    };

    let inv = ghost!(
        AtomicInvariantSC::new(
            ghost!(PAInv {
                perm: perm.into_inner(),
                auth1: auth1.into_inner(),
                auth2: auth2.into_inner(),
            }),
            snapshot!(PARALLEL_ADD()),
        )
        .into_inner()
    );

    thread::scope(|s| {
        // We use move closures to make sure that they do not contain borrows of `Ghost<_>`, since
        // such a borrow would unnecesary consume space in these closures. So, we create the borrows
        // here.
        let mut frag1: Ghost<&mut _> = frag1.borrow_mut();
        let mut frag2: Ghost<&mut _> = frag2.borrow_mut();
        let inv: Ghost<&_> = inv.borrow();
        let atomic = &atomic;

        let t1 = s.spawn(move |tokens: Ghost<Tokens>| {
            atomic.fetch_add(
                2,
                Ordering::SeqCst,
                ghost! { |c: &mut UpdateCommitter| {
                    inv.open(tokens.into_inner(), |inv: &mut PAInv| {
                        inv.auth1.update(&mut *frag1, snapshot!((Some(Excl(true)), Some(Excl(true)))));
                        c.shoot_load(&inv.perm);
                        c.shoot_store(&mut inv.perm);
                    })
                }},
            );
        });

        let t2 = s.spawn(move |tokens: Ghost<Tokens>| {
            atomic.fetch_add(
                2,
                Ordering::SeqCst,
                ghost! { |c: &mut UpdateCommitter| {
                    inv.open(tokens.into_inner(), |inv: &mut PAInv| {
                        inv.auth2.update(&mut *frag2, snapshot!((Some(Excl(true)), Some(Excl(true)))));
                        c.shoot_load(&inv.perm);
                        c.shoot_store(&mut inv.perm);
                    })
                }},
            );
        });

        let _ = t1.join_unwrap();
        let _ = t2.join_unwrap();
    });

    let perm = ghost! {
        let inv = inv.into_inner().into_inner();
        inv.auth1.frag_lemma(&frag1);
        inv.auth2.frag_lemma(&frag2);
        inv.perm
    };

    let n = atomic.into_inner(perm);
    assert!(n == 4i32);
}
