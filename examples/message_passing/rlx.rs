// DEPTH 8

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
        sync::{
            atomic::{AtomicBool, Ordering},
            committer::Committer,
            fence::{fence_acquire, fence_release},
            view::{AtView, SyncView},
        },
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
    Synchronisation(AtView<Box<Perm<PermCell<i32>>>>, Resource<Excl<()>>),
    Readable(Resource<Excl<()>>, Resource<Excl<()>>),
    Invalid,
}

impl Protocol for MessagePassingAtomicInv {
    type Public = (AtomicBool, PermCell<i32>, Id, Id);

    #[logic(inline)]
    fn protocol(self, data: Self::Public) -> bool {
        pearlite! {
            let (atomic, perm, excl_write, excl_read) = data;
            atomic == *self.atomic_own.ward() &&
            match self.state {
                State::NotWrittenYet => forall<t> match self.atomic_own.val().get(t) {
                    Some((b, _)) => !b,
                    None => true
                },
                State::Synchronisation(data_own, tok_write) => excl_write == tok_write.id() && forall<t> match self.atomic_own.val().get(t) {
                    Some((b, view)) => !b || (b && perm == *data_own.val().ward() && data_own.val().val()@ == 1 && data_own.view_logic() <= view),
                    None => true
                },
                State::Readable(tok_write, tok_read) => excl_write == tok_write.id() && excl_read == tok_read.id(),
                State::Invalid => false
            }
        }
    }
}

pub fn message_passing() {
    let (atomic, atomic_own) = AtomicBool::new(false, SyncView::new().borrow_mut());
    let (data, mut data_own) = PermCell::new(0i32);
    let excl_write = Resource::alloc(snapshot!(Excl(())));
    let excl_read = Resource::alloc(snapshot!(Excl(())));

    let inv = AtomicInvariant::new(
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

            unsafe { *data.borrow_mut(ghost!(&mut **data_own)) = 1 }

            let (mut sync_view, at_view) = AtView::new(ghost!(data_own.into_inner())).split();
            let rel_view = fence_release(sync_view);

            atomic.store(
                true,
                ghost! { |c: &mut Committer<_, _, _, Ordering::Relaxed>| {
                    inv.open(tokens.into_inner(), |inv: &mut MessagePassingAtomicInv| {
                        if let State::Synchronisation(_, excl_state) | State::Readable(excl_state, _) = &inv.state {
                            excl.valid_op_lemma(excl_state);
                        }

                        inv.state = State::Synchronisation(at_view.into_inner(), excl.into_inner());
                        c.shoot_store(&mut inv.atomic_own, &mut sync_view, rel_view.into_inner());
                    })
                }},
            );
        });

        let t2 = s.spawn(move |mut tokens: Ghost<Tokens>| {
            let mut excl = ghost!(Some(excl_read.into_inner()));
            let excl_snap = snapshot!(excl);
            let mut data_acq_view = ghost!(None);
            let mut data_at_view = ghost!(None);

            #[invariant(excl == *excl_snap)]
            #[invariant(tokens.contains(MESSAGE_PASSING()))]
            while !atomic.load(ghost! { |c: &Committer<_, bool, Ordering::Relaxed, _>| {
            inv.open(tokens.reborrow(), |inv: &mut MessagePassingAtomicInv| {
                if !*snapshot!(c.val_load()).into_ghost() {
                    return
                }

                if let State::Readable(_, excl_state) = &inv.state {
                    excl.as_mut().unwrap().valid_op_lemma(excl_state);
                }

                let mut sync_view = *SyncView::new();
                let (_, acq) = c.shoot_load(&inv.atomic_own, &mut sync_view);
                data_acq_view = Ghost::new(Some(acq));

                let State::Synchronisation(at_view, tok_write) =
                    std::mem::replace(&mut inv.state, State::Invalid)
                else {
                    unreachable!();
                };

                inv.state = State::Readable(tok_write, excl.take().unwrap());
                data_at_view = Ghost::new(Some(at_view))
            })}}) {}

            let sync_view = fence_acquire(ghost!(data_acq_view.unwrap()));
            let data_own = ghost!(data_at_view.into_inner().unwrap().sync(*sync_view));

            let res = unsafe { data.get(ghost!(&**data_own)) };
            proof_assert!(res == 1i32)
        });

        let _ = t1.join_unwrap();
        let _ = t2.join_unwrap();
    });
}
