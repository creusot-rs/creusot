// DEPTH 8

extern crate creusot_std;

use creusot_std::{
    cell::PermCell,
    ghost::{
        invariant::{AtomicInvariantRelAcq, Protocol, Tokens, declare_namespace},
        perm::Perm,
        resource::Resource,
    },
    logic::{Id, ra::excl::Excl},
    prelude::*,
    std::{
        sync::atomic_relacq::{AtomicI32, LoadCommitter, StoreCommitter},
        thread::{self, JoinHandleExt},
    },
    sync_view::{AtView, SyncView},
};

declare_namespace! { MESSAGE_PASSING }

struct MessagePassingAtomicInv {
    atomic_own: Box<Perm<AtomicI32>>,
    state: State,
}

enum State {
    NotWrittenYet,
    Synchronisation(AtView<Box<Perm<PermCell<i32>>>>, Resource<Excl<()>>),
    Readable(Resource<Excl<()>>, Resource<Excl<()>>),
    Invalid,
}

impl Protocol for MessagePassingAtomicInv {
    type Public = (AtomicI32, PermCell<i32>, Id, Id);

    #[logic(inline)]
    fn protocol(self, data: Self::Public) -> bool {
        pearlite! {
            let (atomic, perm, excl_write, excl_read) = data;
            atomic == *self.atomic_own.ward() &&
            match self.state {
                State::NotWrittenYet => forall<t> match self.atomic_own.val().get(t) {
                    Some((v, _)) => v == 0i32,
                    None => true
                },
                State::Synchronisation(data_own, tok_write) => excl_write == tok_write.id() && forall<t> match self.atomic_own.val().get(t) {
                    Some((v, view)) => v == 0i32 || (v == 1i32 && perm == *data_own.val().ward() && data_own.val().val()@ == 1 && data_own.view_logic().le_log(view)),
                    None => true
                },
                State::Readable(tok_write, tok_read) => excl_write == tok_write.id() && excl_read == tok_read.id(),
                State::Invalid => false
            }
        }
    }
}

pub fn message_passing() {
    let (atomic, atomic_own) = AtomicI32::new(0i32, SyncView::new().borrow_mut());
    let (data, mut data_own) = PermCell::new(0i32);
    let excl_write = Resource::alloc(snapshot!(Excl(())));
    let excl_read = Resource::alloc(snapshot!(Excl(())));

    let inv = AtomicInvariantRelAcq::new(
        ghost!(MessagePassingAtomicInv {
            atomic_own: atomic_own.into_inner(),
            state: State::NotWrittenYet,
        }),
        snapshot!((atomic, data, excl_write.id(), excl_read.id())),
        snapshot!(MESSAGE_PASSING()),
    );

    thread::scope(|s| {
        let inv: Ghost<&_> = inv.borrow();
        let data = &data;
        let atomic = &atomic;

        let t1 = s.spawn(move |tokens: Ghost<Tokens>| {
            let mut excl = ghost!(excl_write.into_inner());

            unsafe {
                *data.borrow_mut(ghost!(&mut **data_own)) = 1;
            }

            atomic.store(
                1,
                ghost! { |c: &mut StoreCommitter<_, _>| {
                    inv.open(tokens.into_inner(), |inv: &mut MessagePassingAtomicInv| {
                        let (mut sync_view, at_view) = AtView::new(ghost!(data_own.into_inner())).into_inner();
                        if let State::Synchronisation(_, excl_state) | State::Readable(excl_state, _) = &inv.state {
                            excl.valid_op_lemma(excl_state);
                        }

                        inv.state = State::Synchronisation(at_view, excl.into_inner());
                        c.shoot(&mut inv.atomic_own, &mut sync_view);
                    })
                }},
            );
        });

        let t2 = s.spawn(move |mut tokens: Ghost<Tokens>| {
            let mut excl = ghost!(Some(excl_read.into_inner()));
            let excl_snap = snapshot!(excl);

            #[invariant(excl == *excl_snap)]
            #[invariant(tokens.contains(MESSAGE_PASSING()))]
            loop {
                let (atomic_res, data_own) = atomic.load(ghost! { |c: &mut LoadCommitter<i32, _>| {
                    inv.open(tokens.reborrow(), |inv: &mut MessagePassingAtomicInv| {
                        if let State::Readable(_, excl_state) = &inv.state {
                            excl.as_mut().unwrap().valid_op_lemma(excl_state);
                        }

                        let mut sync_view = *SyncView::new();
                        let value = snapshot!(c.val()).into_ghost();

                        c.shoot(&inv.atomic_own, &mut sync_view);

                        if *value != 1 {
                            return None;
                        }

                        let State::Synchronisation(at_view, tok_write) = std::mem::replace(&mut inv.state, State::Invalid) else {
                            unreachable!();
                        };

                        inv.state = State::Readable(tok_write, excl.take().unwrap());

                        Some(at_view.into_inner(sync_view))
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
