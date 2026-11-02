use core::sync::atomic::Ordering;

use creusot_std::{
    ghost::{
        invariant::{AtomicInvariant, Protocol, Tokens, declare_namespace},
        perm::Perm,
        resource::{Authority, Fragment},
    },
    logic::{Id, ra::excl::Excl, such_that},
    prelude::*,
    std::{
        sync::{
            atomic::{AtomicI32, ordering::Relaxed},
            committer::Committer,
            view::{ReleaseSyncView, SyncView, Timestamp},
        },
        thread,
    },
};

declare_namespace! { PARALLEL_ADD }

type UpdateCommitter = Committer<AtomicI32, i32, Relaxed, Relaxed>;

struct PAInv {
    perm: Perm<AtomicI32>,
    auth1: Authority<Option<Excl<bool>>>,
    auth2: Authority<Option<Excl<bool>>>,
    t_last: Timestamp,
}

impl Protocol for PAInv {
    type Public = (AtomicI32, Id, Id);

    #[logic]
    fn public(self) -> (AtomicI32, Id, Id) {
        (*self.perm.ward(), self.auth1.id(), self.auth2.id())
    }

    #[logic(inline)]
    fn protocol(self) -> bool {
        pearlite! {
            (forall<t> self.perm.val().contains(&t) ==> t == self.t_last || self.perm.val().contains_logic(t + 1)) &&
            match self.perm.val().lookup(self.t_last) {
                Some((v, _)) =>
                    v@ == if self.auth1@ == Some(Excl(true)) { 2 } else { 0 } +
                    if self.auth2@ == Some(Excl(true)) { 2 } else { 0 },
                None => false,
            }
        }
    }
}

pub fn parallel_add() {
    let mut view = ghost!(SyncView::new().into_inner());
    let (atomic, perm) = AtomicI32::new(0, view.borrow_mut());

    let mut auth1 = ghost!(Authority::alloc().into_inner());
    let mut auth2 = ghost!(Authority::alloc().into_inner());
    let mut frag1 = ghost!(Fragment::new_unit(auth1.id()));
    let mut frag2 = ghost!(Fragment::new_unit(auth2.id()));
    ghost! {
        auth1.update(&mut frag1, snapshot!((Some(Excl(false)), Some(Excl(false)))));
        auth2.update(&mut frag2, snapshot!((Some(Excl(false)), Some(Excl(false)))));
    };

    let timestamp = snapshot!(such_that(|t| perm.val().contains(&t)));

    let inv = ghost!(
        AtomicInvariant::new(
            ghost!(PAInv {
                perm: perm.into_inner(),
                auth1: auth1.into_inner(),
                auth2: auth2.into_inner(),
                t_last: *timestamp.into_ghost(),
            }),
            snapshot!(PARALLEL_ADD()),
        )
        .into_inner()
    );

    thread::scope(|s| {
        s.spawn(|tokens: Ghost<Tokens>| {
            atomic.fetch_add::<_, Relaxed>(
                2,
                Ordering::Relaxed,
                ghost! { |c: &mut UpdateCommitter| {
                    inv.open(tokens.into_inner(), |inv: &mut PAInv| {
                        inv.auth1.update(&mut *frag1, snapshot!((Some(Excl(true)), Some(Excl(true)))));

                        c.shoot_load(&inv.perm, &mut *SyncView::new());
                        c.shoot_store(&mut inv.perm, &mut *SyncView::new(), *ReleaseSyncView::new());

                        inv.t_last += 1int;
                    })
                }},
            );
        });

        s.spawn(|tokens: Ghost<Tokens>| {
            atomic.fetch_add::<_, Relaxed>(
                2,
                Ordering::Relaxed,
                ghost! { |c: &mut UpdateCommitter| {
                    inv.open(tokens.into_inner(), |inv: &mut PAInv| {
                        inv.auth2.update(&mut *frag2, snapshot!((Some(Excl(true)), Some(Excl(true)))));

                        c.shoot_load(&inv.perm, &mut *SyncView::new());
                        c.shoot_store(&mut inv.perm, &mut *SyncView::new(), *ReleaseSyncView::new());

                        inv.t_last += 1int;
                    })
                }},
            );
        });
    });

    let perm = ghost! {
        let inv = inv.into_inner().into_inner();
        inv.auth1.frag_lemma(&frag1);
        inv.auth2.frag_lemma(&frag2);
        inv.perm
    };

    let (n, _) = atomic.into_inner(perm);
    assert!(n == 4i32);
}
