// DEPTH 10

use core::{mem::replace, sync::atomic::Ordering};

use creusot_std::{
    cell::PCell,
    ghost::{
        invariant::{AtomicInvariant, Protocol, Tokens, declare_namespace},
        perm::Perm,
        resource::Resource,
    },
    logic::{Id, ra::excl::Excl},
    prelude::*,
    std::{
        sync::{
            atomic::{AtomicBool, fence_acquire, fence_release, ordering::Relaxed},
            committer::Committer,
            view::{AtView, SyncView},
        },
        thread,
    },
};

declare_namespace! { MESSAGE_PASSING }

type LoadCommitter = Committer<AtomicBool, bool, Relaxed, ()>;
type StoreCommitter = Committer<AtomicBool, bool, (), Relaxed>;

struct MPInv {
    flag_perm: Perm<AtomicBool>,
    state: State,
    public_data: Snapshot<(PCell<i32>, Id, Id)>,
}

enum State {
    NotWrittenYet,
    Synchronisation(AtView<Perm<PCell<i32>>>, Resource<Excl<()>>),
    Readable(Resource<Excl<()>>, Resource<Excl<()>>),
    Invalid,
}

impl Protocol for MPInv {
    type Public = (AtomicBool, PCell<i32>, Id, Id);

    #[logic(inline)]
    fn public(self) -> Self::Public {
        let (data, write_id, read_id) = *self.public_data;
        (*self.flag_perm.ward(), data, write_id, read_id)
    }

    #[logic(inline)]
    fn protocol(self) -> bool {
        pearlite! {
            let (data, write_id, read_id) = *self.public_data;

            match self.state {
                State::NotWrittenYet => forall<t> match self.flag_perm.val().lookup(t) {
                    Some((b, _)) => !b,
                    _ => true
                },
                State::Synchronisation(data_perm, write_token) => {
                    write_id == write_token.id() &&
                    forall<t> match self.flag_perm.val().lookup(t) {
                        Some((true, view)) => {
                            data == *data_perm.val().ward() &&
                            data_perm.val().val() == 42_i32 &&
                            data_perm.view() <= view
                        },
                        _ => true
                    }
                },
                State::Readable(write_token, read_token) => {
                    write_id == write_token.id() &&
                    read_id == read_token.id()
                },
                State::Invalid => false
            }
        }
    }
}

pub fn message_passing() {
    let (flag, flag_perm) = AtomicBool::new(false, SyncView::new().borrow_mut());
    let (data, mut data_perm) = PCell::new(0i32);
    let mut write_excl = ghost!(Resource::alloc(snapshot!(Excl(()))).into_inner());
    let mut read_excl = ghost!(Some(Resource::alloc(snapshot!(Excl(()))).into_inner()));

    let inv = ghost!(AtomicInvariant::new(
        ghost!(MPInv {
            flag_perm: flag_perm.into_inner(),
            state: State::NotWrittenYet,
            public_data: snapshot!((data, write_excl.id(), read_excl.unwrap_logic().id())),
        }),
        snapshot!(MESSAGE_PASSING()),
    ));

    thread::scope(|s| {
        s.spawn(|tokens: Ghost<Tokens>| {
            unsafe { *data.borrow_mut(ghost!(&mut *data_perm)) = 42 }

            let (mut sync_view, data_perm) = AtView::new(ghost!(data_perm.into_inner())).split();
            let rel_view = fence_release(sync_view);

            flag.store(
                true,
                Ordering::Relaxed,
                ghost! { |c: &mut StoreCommitter| {
                    inv.open(tokens.into_inner(), |inv: &mut MPInv| {
                        if let State::Synchronisation(_, write_token)
                        | State::Readable(write_token, _) = &inv.state
                        {
                            write_excl.valid_op_lemma(write_token);
                        }

                        inv.state = State::Synchronisation(data_perm.into_inner(), write_excl.into_inner());
                        c.shoot_store(&mut inv.flag_perm, &mut sync_view, *rel_view);
                    })
                }},
            );
        });

        s.spawn(|mut tokens: Ghost<Tokens>| {
            let old_read_excl = snapshot!(read_excl);
            let mut acq_view = ghost!(None);
            let mut data_perm = ghost!(None);

            #[invariant(read_excl == *old_read_excl)]
            #[invariant(tokens.contains(MESSAGE_PASSING()))]
            while !flag.load(
                Ordering::Relaxed,
                ghost! { |c: &LoadCommitter| {
                    inv.open(tokens.reborrow(), |inv: &mut MPInv| {
                        if !c.val_load() {
                            return
                        }

                        let mut sync_view = *SyncView::new();
                        *acq_view = Some(c.shoot_load(&inv.flag_perm, &mut sync_view));

                        if let State::Readable(_, read_token) = &inv.state {
                            read_excl.as_mut().unwrap().valid_op_lemma(read_token);
                        }

                        let State::Synchronisation(d_perm, write_token) =
                            replace(&mut inv.state, State::Invalid)
                        else {
                            unreachable!();
                        };
                        inv.state = State::Readable(write_token, read_excl.take().unwrap());
                        *data_perm = Some(d_perm)
                    })
                }},
            ) {}

            let sync_view = fence_acquire(ghost!(acq_view.unwrap()));
            let mut data_perm = ghost!(data_perm.into_inner().unwrap().sync(*sync_view));
            let res = unsafe { *data.borrow_mut(ghost!(&mut *data_perm)) };
            assert!(res == 42);
        });
    });
}
