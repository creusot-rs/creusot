use core::{mem::replace, sync::atomic::Ordering};

use creusot_std::{
    cell::PCell,
    ghost::{
        invariant::{AtomicInvariantSC, Protocol, Tokens, declare_namespace},
        perm::Perm,
        resource::Resource,
    },
    logic::{Id, ra::excl::Excl},
    prelude::*,
    std::{
        sync::{
            atomic_sc::{AtomicBool, ordering::SeqCst},
            committer::Committer,
        },
        thread,
    },
};

declare_namespace! { MESSAGE_PASSING }

type LoadCommitter = Committer<AtomicBool, bool, SeqCst, ()>;
type StoreCommitter = Committer<AtomicBool, bool, (), SeqCst>;

struct MPInv {
    flag_perm: Perm<AtomicBool>,
    state: State,
    public_data: Snapshot<(PCell<i32>, Id)>,
}

enum State {
    NotWrittenYet,
    Synchronisation(Perm<PCell<i32>>),
    Readable(Resource<Excl<()>>),
}

impl Protocol for MPInv {
    type Public = (AtomicBool, PCell<i32>, Id);

    #[logic(inline)]
    fn public(self) -> Self::Public {
        let (data, id) = *self.public_data;
        (*self.flag_perm.ward(), data, id)
    }

    #[logic(inline)]
    fn protocol(self) -> bool {
        pearlite! {
            let (_, data, read_excl) = self.public();

            match self.state {
                State::NotWrittenYet => !self.flag_perm.val(),
                State::Synchronisation(data_perm) => {
                    data == *data_perm.ward() &&
                    self.flag_perm.val() &&
                    data_perm.val() == 42_i32
                },
                State::Readable(read_token) => read_excl == read_token.id()
            }
        }
    }
}

pub fn message_passing() {
    let (flag, flag_perm) = AtomicBool::new(false);
    let (data, mut data_perm) = PCell::new(0i32);
    let read_excl = ghost!(Resource::alloc(snapshot!(Excl(()))).into_inner());

    let inv = ghost!(AtomicInvariantSC::new(
        ghost!(MPInv {
            flag_perm: flag_perm.into_inner(),
            state: State::NotWrittenYet,
            public_data: snapshot!((data, read_excl.id())),
        }),
        snapshot!(MESSAGE_PASSING()),
    ));

    thread::scope(|s| {
        s.spawn(|tokens: Ghost<Tokens>| {
            unsafe { *data.borrow_mut(ghost!(&mut *data_perm)) = 42 }

            flag.store(
                true,
                Ordering::SeqCst,
                ghost! { |c: &mut StoreCommitter| {
                    inv.open(tokens.into_inner(), |inv: &mut MPInv| {
                        inv.state = State::Synchronisation(data_perm.into_inner());
                        c.shoot_store(&mut inv.flag_perm);
                    })
                }},
            );
        });

        s.spawn(|mut tokens: Ghost<Tokens>| {
            let mut read_excl = ghost!(Some(read_excl.into_inner()));
            let old_read_excl = snapshot!(read_excl);
            let mut data_perm = ghost!(None);

            #[invariant(read_excl == *old_read_excl)]
            #[invariant(tokens.contains(MESSAGE_PASSING()))]
            while !flag.load(
                Ordering::SeqCst,
                ghost! { |c: &LoadCommitter| {
                    inv.open(tokens.reborrow(), |inv: &mut MPInv| {
                        if !c.val_load() {
                            return
                        }

                        c.shoot_load(&inv.flag_perm);

                        if let State::Readable(read_token) = &inv.state {
                            read_excl.as_mut().unwrap().valid_op_lemma(read_token)
                        }

                        let State::Synchronisation(d_perm) =
                            replace(&mut inv.state, State::Readable(read_excl.take().unwrap()))
                        else {
                            unreachable!();
                        };
                        *data_perm = Some(d_perm);
                    })
                }},
            ) {}

            let data_perm = ghost! { data_perm.as_mut().unwrap() };
            let res = unsafe { *data.borrow_mut(data_perm) };
            assert!(res == 42);
        });
    });
}
