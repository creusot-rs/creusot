// DEPTH 10

extern crate creusot_std;

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
            atomic::{AtomicI32, Ordering},
            committer::Committer,
            view::{ReleaseSyncView, SyncView, Timestamp},
        },
        thread::{self, JoinHandleExt},
    },
};
use std::thread::ScopedJoinHandle;

declare_namespace! { PARALLEL_ADD }

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

struct ParallelAddAtomicInv {
    own: Perm<AtomicI32>,
    auth: Authority<Option<(PR, Int)>>,
    t_last: Timestamp,
}

impl Protocol for ParallelAddAtomicInv {
    type Public = (AtomicI32, Id);

    #[logic]
    fn public(self) -> (AtomicI32, Id) {
        (*self.own.ward(), self.auth.id())
    }

    #[logic(inline)]
    fn protocol(self) -> bool {
        pearlite! {
            (forall<t> self.own.val().contains(t) ==> t == self.t_last || self.own.val().contains(t + 1)) &&
            match self.own.val().get(self.t_last) {
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
    let (atomic, own) = AtomicI32::new(0, SyncView::new().borrow_mut());
    let _ = snapshot!((fraction_1, fraction_add));

    // Create our ghost state
    let mut auth = Authority::alloc();
    let mut frag = ghost!(Fragment::new_unit(auth.id_ghost()));
    ghost! {
        auth.update(&mut frag, snapshot!((Some((PR::from_int(1), 0)), Some((PR::from_int(1), 0)))));
    };

    let timestamp = snapshot!(such_that(|t| own.val().contains(t)));

    // Initialize our invariant
    let inv = AtomicInvariant::new(
        ghost!(ParallelAddAtomicInv {
            own: own.into_inner(),
            auth: auth.into_inner(),
            t_last: *timestamp.into_ghost()
        }),
        snapshot!(PARALLEL_ADD()),
    );

    thread::scope(|s| {
        let inv: Ghost<&_> = inv.borrow();
        let atomic = &atomic;

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
            let h = s.spawn(move |tokens: Ghost<Tokens>| {
                atomic.fetch_add::<_, Ordering::Relaxed>(
                    1,
                    ghost! { |c: &mut Committer<_, _, Ordering::Relaxed, Ordering::Relaxed>| {
                        inv.open(tokens.into_inner(), |inv: &mut ParallelAddAtomicInv| {
                            inv.auth.update(&mut *frag, OptionLocalUpdate(((), 1int)));

                            c.shoot_load(&inv.own, &mut *SyncView::new());
                            c.shoot_store(&mut inv.own, &mut *SyncView::new(), *ReleaseSyncView::new());

                            inv.t_last += 1int;
                        })
                    }},
                );
                frag
            });
            handles.push(h)
        }

        let handles_ = snapshot!(handles);

        // Join the threads
        #[invariant(frag.id() == inv.public().1)]
        #[invariant(frag@ == Some((fraction(produced.len()+1, n@), produced.len())))]
        for h in handles {
            proof_assert!(h == handles_[produced.len() - 1]);
            let f = h.join_unwrap();
            ghost! { frag.join_in(f.into_inner()) };
        }
    });

    final_read(atomic, inv, n, frag);
}

#[requires(inv.public() == (atomic, frag.id()))]
#[requires(frag@ == Some((PR::from_int(1), n@)))]
fn final_read(
    atomic: AtomicI32,
    inv: Ghost<AtomicInvariant<ParallelAddAtomicInv>>,
    n: i32,
    frag: Ghost<Fragment<Option<(PR, Int)>>>,
) {
    let own = ghost! {
        // Destroy the invariant, get back the ownership of the atomic
        let inv = inv.into_inner().into_inner();
        inv.auth.frag_lemma(&frag);
        inv.own
    };

    let mut view = SyncView::new();
    let (x, _) = atomic.into_inner(own, ghost!(&mut *view)); // Non-atomically read the atomic

    proof_assert!(n == x);
}
