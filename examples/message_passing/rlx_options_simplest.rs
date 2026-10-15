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
    let mut sync_view = SyncView::new();
    let (flag, flag_perm) = AtomicBool::new(false, sync_view.borrow_mut());
    let t_initial = snapshot!(flag.get_timestamp(*sync_view));

    let inv = AtomicInvariant::new(
        ghost!(MPInv { flag_perm: flag_perm.into_inner(), t_initial: *t_initial.into_ghost() }),
        snapshot!(MESSAGE_PASSING()),
    );

    thread::scope(|s| {
        let flag = &flag;
        let inv = &inv;

        s.spawn(move |tokens: Ghost<Tokens>| {
            flag.store(
                true,
                ghost! { |c: &mut StoreCommitter| {
                    inv.open(tokens.into_inner(), |inv: &mut MPInv| {
                        c.shoot_store(&mut inv.flag_perm, &mut *sync_view, *ReleaseSyncView::new());
                    })
                }},
            );
        });

        s.spawn(move |mut tokens: Ghost<Tokens>| {
            #[invariant(tokens.contains(MESSAGE_PASSING()))]
            #[invariant(*t_initial <= flag.get_timestamp(*sync_view))]
            while !flag.load(ghost! { |c: &LoadCommitter| {
            inv.open(tokens.reborrow(), |inv: &mut MPInv| {
                if !c.val_load() {
                    return
                }

                c.shoot_load(&inv.flag_perm, &mut *sync_view);
            })}}) {}

            let res = flag.load(ghost! { |c: &LoadCommitter| {
                inv.open(tokens.reborrow(), |inv: &mut MPInv| {
                    c.shoot_load(&inv.flag_perm, &mut *sync_view);
                })
            }});

            proof_assert!(res == true)
        });
    });
}
