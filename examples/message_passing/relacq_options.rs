// DEPTH 8

use core::{mem::swap, sync::atomic::Ordering};

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
            atomic::{
                AtomicBool,
                ordering::{Acquire, Release},
            },
            committer::Committer,
            view::{AtView, SyncView},
        },
        thread,
    },
};

declare_namespace! { MESSAGE_PASSING }

type LoadCommitter = Committer<AtomicBool, bool, Acquire, ()>;
type StoreCommitter = Committer<AtomicBool, bool, (), Release>;

struct MPInv {
    flag_perm: Perm<AtomicBool>,
    data_perm: Option<AtView<Perm<PCell<i32>>>>,
    write_token: Resource<Option<Excl<()>>>,
    read_token: Resource<Option<Excl<()>>>,
    public_data: Snapshot<PCell<i32>>,
}

impl Protocol for MPInv {
    type Public = (AtomicBool, PCell<i32>, Id, Id);

    #[logic(inline)]
    fn public(self) -> Self::Public {
        (*self.flag_perm.ward(), *self.public_data, self.write_token.id(), self.read_token.id())
    }

    #[logic(inline)]
    fn protocol(self) -> bool {
        pearlite! {
            let (_, data, _, _) = self.public();

            forall<t> match self.flag_perm.val().lookup(t) {
                Some((true, view)) => {
                    self.write_token.val() == Some(Excl(())) &&
                    match self.data_perm {
                        Some(data_perm) => {
                            data == *data_perm.val().ward() &&
                            data_perm.val().val() == 42_i32 &&
                            data_perm.view() <= view
                        },
                        None => self.read_token.val() == Some(Excl(())),
                    }
                },
                _ => true
            }
        }
    }
}

pub fn message_passing() {
    let mut view = ghost!(SyncView::new().into_inner());
    let (flag, flag_perm) = AtomicBool::new(false, view.borrow_mut());
    let (data, mut data_perm) = PCell::new(0i32);
    let mut write_excl = ghost!(Resource::alloc(snapshot!(Some(Excl(())))).into_inner());
    let mut read_excl = ghost!(Resource::alloc(snapshot!(Some(Excl(())))).into_inner());

    let inv = ghost!(AtomicInvariant::new(
        ghost!(MPInv {
            flag_perm: flag_perm.into_inner(),
            data_perm: None,
            write_token: Resource::new_unit(write_excl.id()),
            read_token: Resource::new_unit(read_excl.id()),
            public_data: snapshot!(data),
        }),
        snapshot!(MESSAGE_PASSING()),
    ));

    thread::scope(|s| {
        s.spawn(|tokens: Ghost<Tokens>| {
            unsafe { *data.borrow_mut(ghost!(&mut *data_perm)) = 42 }

            flag.store(
                true,
                Ordering::Release,
                ghost! { |c: &mut StoreCommitter| {
                    inv.open(tokens.into_inner(), |inv: &mut MPInv| {
                        write_excl.valid_op_lemma(&inv.write_token);
                        std::mem::swap(&mut inv.write_token, &mut *write_excl);

                        let (mut sync_view, data_perm) = AtView::new(ghost!(data_perm.into_inner())).into_inner();
                        inv.data_perm = Some(data_perm);
                        c.shoot_store(&mut inv.flag_perm, &mut sync_view);
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
                Ordering::Acquire,
                ghost! { |c: &LoadCommitter| {
                    inv.open(tokens.reborrow(), |inv: &mut MPInv| {
                        if !c.val_load() {
                            return
                        }

                        let mut sync_view = *SyncView::new();
                        c.shoot_load(&inv.flag_perm, &mut sync_view);

                        read_excl.valid_op_lemma(&inv.read_token);

                        swap(&mut inv.read_token, &mut *read_excl);
                        *data_perm = Some(inv.data_perm.take().unwrap().sync(sync_view))
                    })
                }},
            ) {}

            let data_perm = ghost!(data_perm.as_mut().unwrap());
            let res = unsafe { *data.borrow_mut(data_perm) };
            assert!(res == 42);
        });
    });
}
