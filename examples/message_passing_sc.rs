extern crate creusot_std;

use creusot_std::{
    cell::PermCell,
    ghost::{
        invariant::{AtomicInvariantSC, Protocol, Tokens, declare_namespace},
        perm::Perm,
        resource::Resource,
    },
    logic::{Id, ra::excl::Excl},
    prelude::*,
    std::{
        sync::atomic_sc::{AtomicBool, LoadCommitter, StoreCommitter},
        thread::{self, JoinHandleExt},
    },
};

declare_namespace! { MESSAGE_PASSING }

struct MessagePassingAtomicInv {
    atomic_own: Box<Perm<AtomicBool>>,
    state: State,
}

enum State {
    NotWrittenYet,
    Synchronisation(Box<Perm<PermCell<i32>>>),
    Readable(Resource<Excl<()>>),
}

impl Protocol for MessagePassingAtomicInv {
    type Public = (AtomicBool, PermCell<i32>, Id);

    #[logic(inline)]
    fn protocol(self, data: Self::Public) -> bool {
        pearlite! {
            data.0 == *self.atomic_own.ward() &&
            match self.state {
                State::NotWrittenYet => !*self.atomic_own.val(),
                State::Synchronisation(data_own) => data.1 == *data_own.ward() && *self.atomic_own.val() && data_own.val()@ == 1,
                State::Readable(tok) => data.2 == tok.id()
            }
        }
    }
}

pub fn message_passing() {
    let (atomic, atomic_own) = AtomicBool::new(false);
    let (data, mut data_own) = PermCell::new(0i32);
    let excl = Resource::alloc(snapshot!(Excl(())));

    let inv = AtomicInvariantSC::new(
        ghost!(MessagePassingAtomicInv {
            atomic_own: atomic_own.into_inner(),
            state: State::NotWrittenYet,
        }),
        snapshot!((atomic, data, excl.id())),
        snapshot!(MESSAGE_PASSING()),
    );

    thread::scope(|s| {
        let inv: Ghost<&_> = inv.borrow();
        let data = &data;
        let atomic = &atomic;

        let t1 = s.spawn(move |tokens: Ghost<Tokens>| {
            unsafe { *data.borrow_mut(ghost!(&mut **data_own)) = 1 }

            atomic.store(
                true,
                ghost! { |c: &mut StoreCommitter<_>| {
                    inv.open(tokens.into_inner(), |inv: &mut MessagePassingAtomicInv| {
                        inv.state = State::Synchronisation(data_own.into_inner());
                        c.shoot(&mut inv.atomic_own);
                    })
                }},
            );
        });

        let t2 = s.spawn(move |mut tokens: Ghost<Tokens>| {
            let mut excl = ghost!(Some(excl.into_inner()));
            let excl_snap = snapshot!(excl);
            let mut data_own = ghost!(None);

            #[invariant(excl == *excl_snap)]
            #[invariant(tokens.contains(MESSAGE_PASSING()))]
            while !atomic.load(ghost! { |c: &LoadCommitter<AtomicBool>| {
            inv.open(tokens.reborrow(), |inv: &mut MessagePassingAtomicInv| {
                if !*snapshot!{ c.val() }.into_ghost() {
                    return
                }

                if let State::Readable(excl_state) = &inv.state {
                    excl.as_mut().unwrap().valid_op_lemma(excl_state)
                }

                c.shoot(&inv.atomic_own);

                let State::Synchronisation(d_own) =
                    std::mem::replace(&mut inv.state, State::Readable(excl.take().unwrap()))
                else {
                    unreachable!();
                };
                data_own = Ghost::new(Some(d_own));
            })}}) {}

            let res = unsafe { data.get(ghost! { data_own.as_ref().unwrap() }) };
            proof_assert!(res == 1i32)
        });

        let _ = t1.join_unwrap();
        let _ = t2.join_unwrap();
    });
}
