extern crate creusot_std;

use creusot_std::{
    ghost::{
        Committer,
        invariant::{AtomicInvariant, Protocol, Tokens, declare_namespace},
        perm::Perm,
        resource::{Authority, Fragment},
    },
    logic::{Id, ra::excl::Excl},
    prelude::*,
    std::{
        sync::AtomicI32,
        thread::{self, JoinHandleExt},
    },
};

declare_namespace! { PARALLEL_ADD }

struct ParallelAddAtomicInv {
    own: Box<Perm<AtomicI32>>,
    auth1: Authority<Option<Excl<bool>>>,
    auth2: Authority<Option<Excl<bool>>>,
}

impl Protocol for ParallelAddAtomicInv {
    type Public = (AtomicI32, Id, Id);

    #[logic(inline)]
    fn protocol(self, data: (AtomicI32, Id, Id)) -> bool {
        pearlite! {
            data == (*self.own.ward(), self.auth1.id(), self.auth2.id()) &&
            self.own.val()@ ==
                if self.auth1@ == Some(Excl(true)) { 2 } else { 0 } +
                if self.auth2@ == Some(Excl(true)) { 2 } else { 0 }
        }
    }
}

#[requires(tokens.contains(PARALLEL_ADD()))]
pub fn parallel_add(mut tokens: Ghost<Tokens>) {
    let (atomic, own) = AtomicI32::new(0);

    // Create our ghost state
    let mut auth1 = Authority::alloc();
    let mut auth2 = Authority::alloc();
    let mut frag1 = ghost!(Fragment::new_unit(auth1.id_ghost()));
    let mut frag2 = ghost!(Fragment::new_unit(auth2.id_ghost()));
    ghost! {
        auth1.update(&mut frag1, snapshot!((Some(Excl(false)), Some(Excl(false)))));
        auth2.update(&mut frag2, snapshot!((Some(Excl(false)), Some(Excl(false)))));
    };

    // Initialize our invariant
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
        // We use move closure to make sure that they do not contain borrows of `Ghost<_>`, since
        // such a borrow would unnecesary consume space in these closures. So, we create the borrows
        // here.
        let mut frag1: Ghost<&mut _> = frag1.borrow_mut();
        let mut frag2: Ghost<&mut _> = frag2.borrow_mut();
        let inv: Ghost<&_> = inv.borrow();
        let atomic = &atomic;

        let t1 = s.spawn(move |tokens: Ghost<Tokens>| {
            atomic.fetch_add(
                2,
                ghost! { #[check(ghost)] |c: &mut Committer| {
                    inv.open(tokens.into_inner(), #[check(ghost)] |inv: &mut ParallelAddAtomicInv| {
                        inv.auth1.update(*frag1, snapshot!((Some(Excl(true)), Some(Excl(true)))));
                        c.shoot(&mut inv.own);
                    })
                }},
            );
        });

        let t2 = s.spawn(move |tokens: Ghost<Tokens>| {
            atomic.fetch_add(
                2,
                ghost! { #[check(ghost)] |c: &mut Committer| {
                    inv.open(tokens.into_inner(), #[check(ghost)] |inv: &mut ParallelAddAtomicInv| {
                        inv.auth2.update(*frag2, snapshot!((Some(Excl(true)), Some(Excl(true)))));
                        c.shoot(&mut inv.own);
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
    let n = atomic.into_inner(own); // Non-atomically read the atomic
    proof_assert!(n == 4i32)
}
