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
        let (p, id) = *self.public_data;
        (*self.flag_perm.ward(), p, id)
    }

    #[logic(inline)]
    fn protocol(self) -> bool {
        pearlite! {
            match self.state {
                State::NotWrittenYet => !self.flag_perm.val(),
                State::Synchronisation(data_perm) => self.public_data.0 == *data_perm.ward() && self.flag_perm.val() && data_perm.val()@ == 1,
                State::Readable(tok) => self.public_data.1 == tok.id()
            }
        }
    }
}

pub fn message_passing() {
    let (flag, flag_perm) = AtomicBool::new(false);
    let (data, mut data_perm) = PCell::new(0i32);
    let excl = ghost!(Resource::alloc(snapshot!(Excl(()))));

    let inv = ghost!(AtomicInvariantSC::new(
        ghost!(MPInv {
            flag_perm: flag_perm.into_inner(),
            state: State::NotWrittenYet,
            public_data: snapshot!((data, excl.id())),
        }),
        snapshot!(MESSAGE_PASSING()),
    ));

    thread::scope(|s| {
        s.spawn(|tokens: Ghost<Tokens>| {
            unsafe { *data.borrow_mut(ghost!(&mut *data_perm)) = 1 }

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
            let mut excl = ghost!(Some(excl.into_inner()));
            let excl_snap = snapshot!(excl);
            let mut data_perm = ghost!(None);

            #[invariant(excl == *excl_snap)]
            #[invariant(tokens.contains(MESSAGE_PASSING()))]
            while !flag.load(Ordering::SeqCst, ghost! { |c: &LoadCommitter| {
                inv.open(tokens.reborrow(), |inv: &mut MPInv| {
                    if !c.val_load() {
                        return
                    }
                    c.shoot_load(&inv.flag_perm);

                    if let State::Readable(excl_state) = &inv.state {
                        excl.as_mut().unwrap().valid_op_lemma(excl_state)
                    }

                    let State::Synchronisation(d_perm) =
                        replace(&mut inv.state, State::Readable(excl.take().unwrap().into_inner()))
                    else {
                        unreachable!();
                    };
                    *data_perm = Some(d_perm);
                })}
            }) {}

            let res = unsafe { *data.borrow_mut(ghost! { data_perm.as_mut().unwrap() }) };
            assert!(res == 1);
        });
    });
}
