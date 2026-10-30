use core::sync::atomic::Ordering;

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
        thread,
    },
};

declare_namespace! { MESSAGE_PASSING }

type LoadCommitter = Committer<AtomicBool, bool, Relaxed, ()>;
type StoreCommitter = Committer<AtomicBool, bool, (), Relaxed>;

struct MPInv {
    flag_perm: Perm<AtomicBool>,
    t_initial: Timestamp,
}

impl Protocol for MPInv {
    type Public = (AtomicBool, Timestamp);

    #[logic(inline)]
    fn public(self) -> Self::Public {
        (*self.flag_perm.ward(), self.t_initial)
    }

    #[logic(inline)]
    fn protocol(self) -> bool {
        pearlite! {
            forall<t> match self.flag_perm.val().lookup(t) {
                Some((false, _)) => self.t_initial == t,
                Some((true, _)) => self.t_initial < t,
                _ => true,
            }
        }
    }
}

pub fn message_passing() {
    let mut view = ghost!(SyncView::new().into_inner());
    let (flag, flag_perm) = AtomicBool::new(false, view.borrow_mut());
    let t_initial = snapshot!(flag.get_timestamp(*view));

    let inv = ghost!(AtomicInvariant::new(
        ghost!(MPInv { flag_perm: flag_perm.into_inner(), t_initial: *t_initial.into_ghost() }),
        snapshot!(MESSAGE_PASSING()),
    ));

    thread::scope(|s| {
        s.spawn(|tokens: Ghost<Tokens>| {
            let mut view = ghost!(*view);

            flag.store(
                true,
                Ordering::Relaxed,
                ghost! { |c: &mut StoreCommitter| {
                    inv.open(tokens.into_inner(), |inv: &mut MPInv| {
                        c.shoot_store(&mut inv.flag_perm, &mut *view, *ReleaseSyncView::new());
                    })
                }},
            );
        });

        s.spawn(|mut tokens: Ghost<Tokens>| {
            let mut view = ghost!(*view);

            #[invariant(tokens.contains(MESSAGE_PASSING()))]
            #[invariant(*t_initial <= flag.get_timestamp(*view))]
            while !flag.load(
                Ordering::Relaxed,
                ghost! { |c: &LoadCommitter| {
                    inv.open(tokens.reborrow(), |inv: &mut MPInv| {
                        if !c.val_load() {
                            return
                        }

                        c.shoot_load(&inv.flag_perm, &mut *view);
                    })
                }},
            ) {}

            let res = flag.load(
                Ordering::Relaxed,
                ghost! { |c: &LoadCommitter| {
                    inv.open(tokens.reborrow(), |inv: &mut MPInv| {
                        c.shoot_load(&inv.flag_perm, &mut *view);
                    })
                }},
            );
            assert!(res == true);
        });
    });
}
