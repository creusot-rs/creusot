extern crate creusot_std;

use creusot_std::{
    ghost::{
        invariant::{AtomicInvariant, Protocol, Tokens, declare_namespace},
        perm::Perm,
    },
    prelude::*,
    std::{
        sync::{
            atomic::{AtomicBool, ordering::Relaxed},
            committer::Committer,
            view::{HasTimestamp, ReleaseSyncView, SyncView, Timestamp},
        },
        thread::{self, JoinHandleExt},
    },
};

declare_namespace! { MESSAGE_PASSING }

struct MessagePassingAtomicInv {
    atomic_own: Perm<AtomicBool>,
    t_initial: Timestamp,
}

impl Protocol for MessagePassingAtomicInv {
    type Public = (AtomicBool, Timestamp);

    #[logic(inline)]
    fn public(self) -> Self::Public {
        (*self.atomic_own.ward(), self.t_initial)
    }

    #[logic(inline)]
    fn protocol(self) -> bool {
        pearlite! {
            forall<t> match self.atomic_own.val().get(t) {
                Some((false, _)) => self.t_initial == t,
                Some((true, _)) => self.t_initial < t,
                _ => true,
            }
        }
    }
}

pub fn message_passing() {
    let mut sync_view = SyncView::new();
    let (atomic, atomic_own) = AtomicBool::new(false, sync_view.borrow_mut());

    let inv = AtomicInvariant::new(
        ghost!(MessagePassingAtomicInv {
            atomic_own: atomic_own.into_inner(),
            t_initial: *snapshot!(atomic.get_timestamp(*sync_view)).into_ghost(),
        }),
        snapshot!(MESSAGE_PASSING()),
    );

    thread::scope(|s| {
        let inv: Ghost<&_> = inv.borrow();
        let atomic = &atomic;

        let t1 = s.spawn(move |tokens: Ghost<Tokens>| {
            atomic.store(
                true,
                ghost! { |c: &mut Committer<_, _, _, Relaxed>| {
                    inv.open(tokens.into_inner(), |inv: &mut MessagePassingAtomicInv| {
                        c.shoot_store(&mut inv.atomic_own, &mut *sync_view, *ReleaseSyncView::new());
                    })
                }},
            );
        });

        let t2 = s.spawn(move |mut tokens: Ghost<Tokens>| {
            #[invariant(tokens.contains(MESSAGE_PASSING()))]
            #[invariant(atomic.get_timestamp(*sync_view) >= inv.public().1)]
            while !atomic.load(ghost! { |c: &Committer<_, bool, Relaxed, _>| {
            inv.open(tokens.reborrow(), |inv: &mut MessagePassingAtomicInv| {
                if !*snapshot!(c.val_load()).into_ghost() {
                    return
                }

                c.shoot_load(&inv.atomic_own, &mut *sync_view);
            })}}) {}

            let res = atomic.load(ghost! { |c: &Committer<_, bool, Relaxed, _>| {
                inv.open(tokens.reborrow(), |inv: &mut MessagePassingAtomicInv| {
                    c.shoot_load(&inv.atomic_own, &mut *sync_view);
                })
            }});

            proof_assert!(res == true)
        });

        let _ = t1.join_unwrap();
        let _ = t2.join_unwrap();
    });
}
