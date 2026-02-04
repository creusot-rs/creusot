// TIME 3

extern crate creusot_std;

use creusot_std::{
    ghost::{
        Committer,
        invariant::{AtomicInvariant, Protocol, Tokens, declare_namespace},
        perm::Perm,
        resource::{Authority, Fragment},
    },
    logic::{Id, ra::option::OptionLocalUpdate, real::PositiveReal as PR},
    prelude::{vec, *},
    std::{
        sync::AtomicI32,
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
    own: Box<Perm<AtomicI32>>,
    auth: Authority<Option<(PR, Int)>>,
}

impl Protocol for ParallelAddAtomicInv {
    type Public = (AtomicI32, Id);

    #[logic(inline)]
    fn protocol(self, data: (AtomicI32, Id)) -> bool {
        pearlite! {
            data == (*self.own.ward(), self.auth.id()) &&
            match self.auth@ {
                None => false,
                Some((q, n)) =>
                    q == PR::from_int(1) &&
                    exists<k: Int> n - self.own.val()@ == k * Int::pow2(32)
            }
        }
    }
}

#[requires(tokens.contains(PARALLEL_ADD()))]
#[requires(n@ >= 0)]
pub fn parallel_add(mut tokens: Ghost<Tokens>, n: i32) {
    let (atomic, own) = AtomicI32::new(0);
    let _ = snapshot!((fraction_1, fraction_add));

    // Create our ghost state
    let mut auth = Authority::alloc();
    let mut frag = ghost!(Fragment::new_unit(auth.id_ghost()));
    ghost! {
        auth.update(&mut frag, snapshot!((Some((PR::from_int(1), 0)), Some((PR::from_int(1), 0)))));
    };

    // Initialize our invariant
    let inv = AtomicInvariant::new(
        ghost!(ParallelAddAtomicInv { own: own.into_inner(), auth: auth.into_inner() }),
        snapshot!((atomic, frag.id())),
        snapshot!(PARALLEL_ADD()),
    );

    thread::scope(|s| {
        let inv: Ghost<&_> = inv.borrow();
        let atomic = &atomic;

        // Spawn the threads

        // I wish we could build the handles vector with a map iterator, but the proof
        // goals end up being too large, and the SMT solvers just give up proving.
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
                atomic.fetch_add(
                    1,
                    ghost! { |c: &mut Committer| {
                        inv.open(tokens.into_inner(), |inv: &mut ParallelAddAtomicInv| {
                            inv.auth.update(&mut *frag, OptionLocalUpdate(((), 1int)));
                            c.shoot(&mut inv.own);
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

    let own = ghost! {
        // Destroy the invariant, get back the ownership of the atomic
        let inv = inv.into_inner().into_inner();
        proof_assert!(inv.auth@.unwrap_logic().0 == PR::from_int(1));
        inv.auth.frag_lemma(&frag);
        inv.own
    };
    let x = atomic.into_inner(own); // Non-atomically read the atomic
    proof_assert!(n == x)
}
