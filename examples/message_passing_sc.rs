extern crate creusot_std;

use creusot_std::{
    cell::PermCell,
    ghost::{
        invariant::{AtomicInvariant, Protocol, Tokens, declare_namespace},
        perm::Perm,
        resource::Resource,
    },
    logic::{Id, ra::excl::Excl},
    prelude::*,
    std::{
        sync::atomic_sc::{AtomicI32, LoadCommitter, StoreCommitter},
        thread::{self, JoinHandleExt},
    },
};

declare_namespace! { MESSAGE_PASSING }

struct MessagePassingAtomicInv {
    atomic_own: Box<Perm<AtomicI32>>,
    state: State,
}

enum State {
    NotWrittenYet,
    Synchronisation(Box<Perm<PermCell<i32>>>),
    Readable(Resource<Excl<()>>),
}

impl Protocol for MessagePassingAtomicInv {
    type Public = (AtomicI32, PermCell<i32>, Id);

    #[logic(inline)]
    fn protocol(self, data: Self::Public) -> bool {
        pearlite! {
            data.0 == *self.atomic_own.ward() &&
            match self.state {
                State::NotWrittenYet => self.atomic_own.val()@ == 0,
                State::Synchronisation(data_own) => data.1 == *data_own.ward() && self.atomic_own.val()@ == 1 && data_own.val()@ == 1,
                State::Readable(tok) => data.2 == tok.id()
            }
        }
    }
}

pub fn message_passing() {
    let (atomic, atomic_own) = AtomicI32::new(0i32);
    let (data, mut data_own) = PermCell::new(0i32);
    let excl = Resource::alloc(snapshot!(Excl(())));

    let inv = AtomicInvariant::new(
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
            unsafe {
                *data.borrow_mut(ghost!(&mut **data_own)) = 1;
            }

            atomic.store(
                1,
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

            #[invariant(excl == *excl_snap)]
            #[invariant(tokens.contains(MESSAGE_PASSING()))]
            loop {
                let (atomic_res, data_own) = atomic.load(ghost! { |c: &mut LoadCommitter<_>| {
                    inv.open(tokens.reborrow(), |inv: &mut MessagePassingAtomicInv| {
                        if let State::Readable(excl_state) = &inv.state {
                            excl.as_mut().unwrap().valid_op_lemma(excl_state);
                        }

                        c.shoot(&inv.atomic_own);

                        match &inv.state {
                            State::Synchronisation(_) => {
                                let State::Synchronisation(data_own) = std::mem::replace(&mut inv.state, State::Readable(excl.take().unwrap())) else {
                                    unreachable!();
                                };
                                Some(data_own)
                            }
                            _ => None
                        }
                    })
                }});

                if atomic_res != 1 {
                    continue;
                }

                let data_own = ghost! { data_own.into_inner().unwrap() };
                let res = unsafe { data.get(ghost! { &**data_own }) };
                proof_assert!(res == 1i32);
                break;
            }
        });

        let _ = t1.join_unwrap();
        let _ = t2.join_unwrap();
    });
}
