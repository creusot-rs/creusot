extern crate creusot_contracts;
use creusot_contracts::{
    ghost::{
        Committer,
        invariant::{AtomicInvariant, Protocol, declare_namespace},
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

    #[logic]
    fn protocol(self, data: (AtomicI32, Id, Id)) -> bool {
        pearlite! {
            self.own.tied() == data.0 &&
            self.auth1.id() == data.1 &&
            self.auth2.id() == data.2 &&
            self.auth1@.auth() != None &&
            self.auth2@.auth() != None
        }
    }
}

pub fn parallel_add() {
    let (atomic, own) = AtomicI32Own::new(0);

    let false_ = Some(Excl(false));
    let true_ = Some(Excl(true));

    let mut auth1 = Resource::alloc(snapshot!(Auth::new(Some(false_), false_)));
    let mut auth2 = Resource::alloc(snapshot!(Auth::new(Some(false_), false_)));
    let mut frag1 = ghost! {auth1.split_off(snapshot!(Auth::new_frag(false_)), snapshot!(Auth::new_auth(false_)))};
    let frag2 = ghost! {auth2.split_off(snapshot!(Auth::new_frag(false_)), snapshot!(Auth::new_auth(false_)))};

    let inv = AtomicInvariant::new(
        ghost!(ParallelAddAtomicInv {
            own: own.into_inner(),
            auth1: auth1.into_inner(),
            auth2: auth2.into_inner()
        }),
        snapshot!((atomic, frag1.id(), frag2.id())),
        snapshot!(PARALLEL_ADD()),
    );

    let inv_borrow = inv.borrow();
    let mut frag1_borrow = frag1.borrow_mut();

    thread::scope(|s| {
        let t1 = s.spawn(|tokens| {
            atomic.store(
                1,
                ghost! {
                    #[check(ghost)]
                    |c: &mut Committer| {
                        inv_borrow.open(tokens.into_inner(), #[check(ghost)] move |inv: &mut ParallelAddAtomicInv| {
                            inv.auth1.join_in(frag1_borrow.take());
                            inv.auth1.update(ViewUpdate(snapshot!(|()| (true_, true_))));
                            **frag1_borrow = inv.auth1.split_off(snapshot!(Auth::new_frag(true_)), snapshot!(Auth::new_auth(true_)));
                            c.shoot(&mut inv.own);
                        })
                    }
                },
            );
        });

        let t2 = s.spawn(|_| {});

        let _ = t1.join_unwrap();
        let _ = t2.join_unwrap();

        // proof_assert!(own.val() == 1i32);
    });
}
