extern crate creusot_std;

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
            atomic_sc::{
                AtomicBool,
                ordering::{self, SeqCst},
            },
            committer::Committer,
        },
        thread,
    },
};
use std::mem::swap;

declare_namespace! { MESSAGE_PASSING }

type LoadCommitter = Committer<AtomicBool, bool, SeqCst, ordering::None>;
type StoreCommitter = Committer<AtomicBool, bool, ordering::None, SeqCst>;

struct MPInv {
    flag_perm: Perm<AtomicBool>,
    data_perm: Option<Perm<PCell<i32>>>,
    data: Snapshot<PCell<i32>>,
    tok: Resource<Option<Excl<()>>>,
}

impl Protocol for MPInv {
    type Public = (AtomicBool, PCell<i32>, Id);

    #[logic(inline)]
    fn public(self) -> Self::Public {
        (*self.flag_perm.ward(), *self.data, self.tok.id())
    }

    #[logic(inline)]
    fn protocol(self) -> bool {
        pearlite! {
            !self.flag_perm.val() ||
             match self.data_perm {
                Some(data_perm) => *self.data == *data_perm.ward() && self.flag_perm.val() && data_perm.val()@ == 42,
                None => self.tok.val() == Some(Excl(())),
            }
        }
    }
}

pub fn message_passing() {
    let (flag, flag_perm) = AtomicBool::new(false);
    let (data, mut data_perm) = PCell::new(0i32);

    let mut excl = Resource::alloc(snapshot!(Some(Excl(()))));
    let inv = AtomicInvariantSC::new(
        ghost!(MPInv {
            flag_perm: flag_perm.into_inner(),
            data_perm: None,
            data: snapshot!(data),
            tok: Resource::new_unit(excl.id_ghost())
        }),
        snapshot!(MESSAGE_PASSING()),
    );

    thread::scope(|s| {
        s.spawn(|tokens: Ghost<Tokens>| {
            unsafe { *data.borrow_mut(ghost!(&mut *data_perm)) = 42 }
            flag.store(
                true,
                ghost! { |c: &mut StoreCommitter| {
                    inv.open(tokens.into_inner(), |inv: &mut MPInv| {
                        inv.data_perm = Some(data_perm.into_inner());
                        c.shoot_store(&mut inv.flag_perm);
                    })
                }},
            );
        });

        s.spawn(|mut tokens: Ghost<Tokens>| {
            let old_excl = snapshot!(excl);
            let mut data_perm = ghost!(None);

            #[invariant(excl == *old_excl)]
            #[invariant(tokens.contains(MESSAGE_PASSING()))]
            while !flag.load(ghost! { |c: &LoadCommitter| {
                inv.open(tokens.reborrow(), |inv: &mut MPInv| {
                    if !c.val_load_ghost() {
                        return
                    }

                    excl.valid_op_lemma(&inv.tok);
                    swap(&mut inv.tok, &mut *excl);

                    c.shoot_load(&mut inv.flag_perm);
                    *data_perm = inv.data_perm.take()
                })
            }}) {}

            let data_perm = ghost!(data_perm.into_inner().unwrap());
            let res = unsafe { data.get(data_perm.borrow()) };
            proof_assert!(res == 42_i32);
        });
    });
}
