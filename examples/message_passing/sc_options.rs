use core::{mem::swap, sync::atomic::Ordering};

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
    data_perm: Option<Perm<PCell<i32>>>,
    read_token: Resource<Option<Excl<()>>>,
    public_data: Snapshot<PCell<i32>>,
}

impl Protocol for MPInv {
    type Public = (AtomicBool, PCell<i32>, Id);

    #[logic(inline)]
    fn public(self) -> Self::Public {
        (*self.flag_perm.ward(), *self.public_data, self.read_token.id())
    }

    #[logic(inline)]
    fn protocol(self) -> bool {
        pearlite! {
            let (_, data, _) = self.public();

            !self.flag_perm.val() ||
            match self.data_perm {
                Some(data_perm) => {
                    data == *data_perm.ward() &&
                    self.flag_perm.val() &&
                    data_perm.val() == 42_i32
                },
                None => self.read_token.val() == Some(Excl(())),
            }
        }
    }
}

pub fn message_passing() {
    let (flag, flag_perm) = AtomicBool::new(false);
    let (data, mut data_perm) = PCell::new(0i32);
    let mut read_excl = ghost!(Resource::alloc(snapshot!(Some(Excl(())))).into_inner());

    let inv = ghost!(AtomicInvariantSC::new(
        ghost!(MPInv {
            flag_perm: flag_perm.into_inner(),
            data_perm: None,
            public_data: snapshot!(data),
            read_token: Resource::new_unit(read_excl.id())
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
                        inv.data_perm = Some(data_perm.into_inner());
                        c.shoot_store(&mut inv.flag_perm);
                    })
                }},
            );
        });

        s.spawn(|mut tokens: Ghost<Tokens>| {
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

                        c.shoot_load(&mut inv.flag_perm);

                        read_excl.valid_op_lemma(&inv.read_token);

                        swap(&mut inv.read_token, &mut *read_excl);
                        *data_perm = inv.data_perm.take()
                    })
                }},
            ) {}

            let data_perm = ghost!(data_perm.as_mut().unwrap());
            let res = unsafe { *data.borrow_mut(data_perm) };
            assert!(res == 42);
        });
    });
}
