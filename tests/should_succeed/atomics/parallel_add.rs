extern crate creusot_contracts;
use creusot_contracts::{
    ghost::{
        Committer,
        invariant::{AtomicInvariant, Protocol, Tokens, declare_namespace},
        resource::Resource,
    },
    logic::{
        Id,
        ra::{auth::Auth, excl::Excl, view::ViewUpdate},
    },
    prelude::*,
    std::{
        sync::{AtomicI32, AtomicI32Own},
        thread::{self, JoinHandleExt},
    },
};

declare_namespace! { PARALLEL_ADD }

struct ParallelAddAtomicInv {
    own: AtomicI32Own,
    auth1: Resource<Auth<Option<Excl<bool>>>>,
    auth2: Resource<Auth<Option<Excl<bool>>>>,
}

impl Protocol for ParallelAddAtomicInv {
    type Public = (AtomicI32, Id, Id);

    #[logic(inline)]
    fn protocol(self, data: (AtomicI32, Id, Id)) -> bool {
        pearlite! {
            self.own.tied() == data.0 &&
            self.auth1.id() == data.1 &&
            self.auth2.id() == data.2 &&
            self.auth1@.auth() != None &&
            self.auth2@.auth() != None &&
            self.own.val()@ ==
                if self.auth1@.auth().unwrap_logic().unwrap_logic().0 { 1 } else { 0 } +
                if self.auth2@.auth().unwrap_logic().unwrap_logic().0 { 1 } else { 0 }
        }
    }
}

#[requires(tokens.contains(PARALLEL_ADD()))]
pub fn parallel_add(mut tokens: Ghost<Tokens>) {
    let (atomic, own) = AtomicI32Own::new(0);

    let false_ = Some(Excl(false));

    let mut auth1 = Resource::alloc(snapshot!(Auth::new(Some(false_), false_)));
    let mut auth2 = Resource::alloc(snapshot!(Auth::new(Some(false_), false_)));
    let mut frag1 = ghost! {auth1.split_off(snapshot!(Auth::new_frag(false_)), snapshot!(Auth::new_auth(false_)))};
    let mut frag2 = ghost! {auth2.split_off(snapshot!(Auth::new_frag(false_)), snapshot!(Auth::new_auth(false_)))};

    let inv = AtomicInvariant::new(
        ghost!(ParallelAddAtomicInv {
            own: own.into_inner(),
            auth1: auth1.into_inner(),
            auth2: auth2.into_inner()
        }),
        snapshot!((atomic, frag1.id(), frag2.id())),
        snapshot!(PARALLEL_ADD()),
    );

    thread::scope(|s| {
        let mut frag1 = frag1.borrow_mut();
        let mut frag2 = frag2.borrow_mut();

        let t1 = s.spawn(|tokens| {
            let inv = &inv;
            let true_ = Some(Excl(true));

            atomic.fetch_add(
                1,
                ghost! {
                    #[check(ghost)]
                    |c: &mut Committer| {
                        inv.open(tokens.into_inner(), #[check(ghost)] move |inv: &mut ParallelAddAtomicInv| {
                            proof_assert!(!(frag1@.frag().unwrap_logic().0));
                            inv.auth1.join_in(frag1.take());
                            inv.auth1.update(ViewUpdate(snapshot!(|()| (true_, true_))));
                            **frag1 = inv.auth1.split_off(snapshot!(Auth::new_frag(true_)), snapshot!(Auth::new_auth(true_)));
                            c.shoot(&mut inv.own);
                        })
                    }
                },
            );
        });

        let t2 = s.spawn(|tokens| {
            let inv = &inv;
            let true_ = Some(Excl(true));

            atomic.fetch_add(
                1,
                ghost! {
                    #[check(ghost)]
                    |c: &mut Committer| {
                        inv.open(tokens.into_inner(), #[check(ghost)] move |inv: &mut ParallelAddAtomicInv| {
                            proof_assert!(!(frag2@.frag().unwrap_logic().0));
                            inv.auth2.join_in(frag2.take());
                            inv.auth2.update(ViewUpdate(snapshot!(|()| (true_, true_))));
                            **frag2 = inv.auth2.split_off(snapshot!(Auth::new_frag(true_)), snapshot!(Auth::new_auth(true_)));
                            c.shoot(&mut inv.own);
                        })
                    }
                },
            );
        });

        let _ = t1.join_unwrap();
        let _ = t2.join_unwrap();
    });

    ghost! {
        inv.open(tokens.into_inner(), #[check(ghost)] move |inv: &mut ParallelAddAtomicInv| {
            inv.auth1.join_in(frag1.take());
            inv.auth2.join_in(frag2.take());

            proof_assert!(inv.auth1@.auth().unwrap_logic().unwrap_logic().0);
            proof_assert!(inv.auth2@.auth().unwrap_logic().unwrap_logic().0);

            proof_assert!(inv.own.val() == 2i32);
        })
    };
}
