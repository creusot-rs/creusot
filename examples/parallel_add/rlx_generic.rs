// DEPTH 10

use core::sync::atomic::Ordering;

use creusot_std::{
    ghost::{
        invariant::{AtomicInvariant, Protocol, Tokens, declare_namespace},
        perm::Perm,
        resource::{Authority, Fragment},
    },
    logic::{Id, ra::option::OptionLocalUpdate, real::PositiveReal as PR, such_that},
    prelude::{vec, *},
    std::{
        sync::{
            atomic::{AtomicI32, ordering::Relaxed},
            committer::Committer,
            view::{ReleaseSyncView, SyncView, Timestamp},
        },
        thread::{self, JoinHandleExt},
    },
};
use std::thread::ScopedJoinHandle;

declare_namespace! { PARALLEL_ADD }

type UpdateCommitter = Committer<AtomicI32, i32, Relaxed, Relaxed>;

#[logic]
fn fraction(i: Int, n: Int) -> PR {
    pearlite! { PR::from_int(i) / PR::from_int(n+1) }
}

#[logic]
#[ensures(fraction(n+1, n) == PR::from_int(1))]
fn fraction_1(n: Int) {
    let _ = PR::ext_eq;
}

#[logic]
#[requires(a > 0 && b > 0)]
#[ensures(fraction(a, n) + fraction(b, n) == fraction(a+b, n))]
fn fraction_add(a: Int, b: Int, n: Int) {
    let _ = PR::ext_eq;
}

struct PAInv {
    perm: Perm<AtomicI32>,
    auth: Authority<Option<(PR, Int)>>,
    t_last: Timestamp,
}

impl Protocol for PAInv {
    type Public = (AtomicI32, Id);

    #[logic]
    fn public(self) -> (AtomicI32, Id) {
        (*self.perm.ward(), self.auth.id())
    }

    #[logic(inline)]
    fn protocol(self) -> bool {
        pearlite! {
            (forall<t> self.perm.val().contains(&t) ==> t == self.t_last || self.perm.val().contains_logic(t + 1)) &&
            match self.perm.val().lookup(self.t_last) {
                Some((v, _)) =>
                  exists<k: Int>
                    self.auth@ == Some((PR::from_int(1), k * Int::pow2(32) + v@)),
                None => false,
            }
        }
    }
}

#[requires(n@ >= 0)]
pub fn parallel_add(n: i32) {
    let mut view = ghost!(SyncView::new().into_inner());
    let (atomic, perm) = AtomicI32::new(0, view.borrow_mut());
    let _ = snapshot!((fraction_1, fraction_add));

    let mut auth = ghost!(Authority::alloc().into_inner());
    let mut frag = ghost!(Fragment::new_unit(auth.id()));
    ghost! {
        auth.update(&mut frag, snapshot!((Some((PR::from_int(1), 0)), Some((PR::from_int(1), 0)))));
    };

    let timestamp = snapshot!(such_that(|t| perm.val().contains(&t)));

    let inv = ghost!(
        AtomicInvariant::new(
            ghost!(PAInv {
                perm: perm.into_inner(),
                auth: auth.into_inner(),
                t_last: *timestamp.into_ghost(),
            }),
            snapshot!(PARALLEL_ADD()),
        )
        .into_inner()
    );

    thread::scope(|s| {
        let mut handles: Vec<ScopedJoinHandle<_>> = vec![];

        #[invariant(frag.id() == inv.public().1)]
        #[invariant(frag@ == Some((fraction(n@+1-produced.len(), n@), 0)))]
        #[invariant(handles@.len() == produced.len())]
        #[invariant(forall<j, f: Ghost<Fragment<_>>>
            0 <= j && j < produced.len() && handles@[j].valid_result(f) ==>
            f@ == Some((fraction(1, n@), 1)) && f.id() == inv.public().1
        )]
        for _ in 0..n {
            let f1 = snapshot! { Some((fraction(1, n@), 0)) };
            let f2 = snapshot! { Some((fraction(n@+1-produced.len(), n@), 0)) };
            let mut frag = ghost! { frag.split_off(f1, f2) };
            let h = s.spawn(|tokens: Ghost<Tokens>| {
                atomic.fetch_add::<_, Relaxed>(
                    1,
                    Ordering::Relaxed,
                    ghost! { |c: &mut UpdateCommitter| {
                        inv.open(tokens.into_inner(), |inv: &mut PAInv| {
                            inv.auth.update(&mut *frag, OptionLocalUpdate(((), 1int)));

                            c.shoot_load(&inv.perm, &mut *SyncView::new());
                            c.shoot_store(&mut inv.perm, &mut *SyncView::new(), *ReleaseSyncView::new());

                            inv.t_last += 1int;
                        })
                    }},
                );
                proof_assert!(
                    frag@ == Some((fraction(1, n@), 1)) &&
                    frag.id() == inv.public().1);
                frag
            });
            handles.push(h)
        }

        let handles_ = snapshot!(handles);

        #[invariant(frag.id() == inv.public().1)]
        #[invariant(frag@ == Some((fraction(produced.len()+1, n@), produced.len())))]
        for h in handles {
            proof_assert!(h == handles_[produced.len() - 1]);
            let f = h.join_unwrap();
            ghost! { frag.join_in(f.into_inner()) };
        }
        proof_assert!(frag@ == Some((PR::from_int(1), n@)));
    });

    let perm = ghost! {
        let inv = inv.into_inner().into_inner();
        inv.auth.frag_lemma(&frag);
        inv.perm
    };

    let (x, _) = atomic.into_inner(perm);
    assert!(n == x);
}
