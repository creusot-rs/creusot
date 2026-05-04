// TIME 5

extern crate creusot_std;

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
            atomic::{AtomicI32, Ordering},
            committer::Committer,
            view::{ReleaseSyncView, SyncView, Timestamp},
        },
        thread::{self, JoinHandleExt},
    },
};

declare_namespace! { PARALLEL_ADD }

struct ParallelAddAtomicInv {
    own: Perm<AtomicI32>,
    auth1: Authority<Option<Excl<bool>>>,
    auth2: Authority<Option<Excl<bool>>>,
    t_last: Timestamp,
}

impl Protocol for ParallelAddAtomicInv {
    type Public = (AtomicI32, Id, Id);

    #[logic]
    fn public(self) -> (AtomicI32, Id, Id) {
        (*self.own.ward(), self.auth1.id(), self.auth2.id())
    }

    #[logic(inline)]
    fn protocol(self) -> bool {
        pearlite! {
            (forall<t> self.own.val().contains(t) ==> t == self.t_last || self.own.val().contains(t + 1)) &&
            match self.own.val().get(self.t_last) {
                Some((v, _)) =>
                    v@ == if self.auth1@ == Some(Excl(true)) { 2 } else { 0 } +
                    if self.auth2@ == Some(Excl(true)) { 2 } else { 0 },
                None => false,
            }
        }
    }
}

pub fn parallel_add() {
    let (atomic, own) = AtomicI32::new(0, SyncView::new().borrow_mut());

    // Create our ghost state
    let mut auth1 = Authority::alloc();
    let mut auth2 = Authority::alloc();
    let mut frag1 = ghost!(Fragment::new_unit(auth1.id_ghost()));
    let mut frag2 = ghost!(Fragment::new_unit(auth2.id_ghost()));
    ghost! {
        auth1.update(&mut frag1, snapshot!((Some(Excl(false)), Some(Excl(false)))));
        auth2.update(&mut frag2, snapshot!((Some(Excl(false)), Some(Excl(false)))));
    };

    let timestamp = snapshot!(such_that(|t| own.val().contains(t)));

    // Initialize our invariant
    let inv = AtomicInvariant::new(
        ghost!(ParallelAddAtomicInv {
            own: own.into_inner(),
            auth1: auth1.into_inner(),
            auth2: auth2.into_inner(),
            t_last: *timestamp.into_ghost()
        }),
        snapshot!(PARALLEL_ADD()),
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
            atomic.fetch_add::<_, Ordering::Relaxed>(
                2,
                ghost! { |c: &mut Committer<_, _, Ordering::Relaxed, Ordering::Relaxed>| {
                    inv.open(tokens.into_inner(), |inv: &mut ParallelAddAtomicInv| {
                        inv.auth1.update(*frag1, snapshot!((Some(Excl(true)), Some(Excl(true)))));

                        c.shoot_load(&inv.own, &mut *SyncView::new());
                        c.shoot_store(&mut inv.own, &mut *SyncView::new(), *ReleaseSyncView::new());

                        inv.t_last += 1int;
                    })
                }},
            );
        });

        let t2 = s.spawn(move |tokens: Ghost<Tokens>| {
            atomic.fetch_add::<_, Ordering::Relaxed>(
                2,
                ghost! { |c: &mut Committer<_, _, Ordering::Relaxed, Ordering::Relaxed>| {
                    inv.open(tokens.into_inner(), |inv: &mut ParallelAddAtomicInv| {
                        inv.auth2.update(*frag2, snapshot!((Some(Excl(true)), Some(Excl(true)))));

                        c.shoot_load(&inv.own, &mut *SyncView::new());
                        c.shoot_store(&mut inv.own, &mut *SyncView::new(), *ReleaseSyncView::new());

                        inv.t_last += 1int;
                    })
                }},
            );
        });

        let _ = t1.join_unwrap();
        let _ = t2.join_unwrap();
    });

    let own = ghost! {
        // Destroy the invariant, get back the ownership of the atomic
        let inv = inv.into_inner().into_inner();
        inv.auth1.frag_lemma(&frag1);
        inv.auth2.frag_lemma(&frag2);
        inv.own
    };

    let mut view = SyncView::new();
    let (n, _) = atomic.into_inner(own, ghost!(&mut *view)); // Non-atomically read the atomic
    proof_assert!(n == 4i32)
}
