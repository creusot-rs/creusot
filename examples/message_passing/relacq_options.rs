// DEPTH 8

extern crate creusot_std;

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
        thread::{self, JoinHandleExt},
    },
};
use std::mem::swap;

declare_namespace! { MESSAGE_PASSING }

struct MPInv {
    flag_perm: Perm<AtomicBool>,
    at_view: Option<AtView<Perm<PCell<i32>>>>,
    tok_write: Resource<Option<Excl<()>>>,
    tok_read: Resource<Option<Excl<()>>>,
    data: Snapshot<PCell<i32>>,
}

impl Protocol for MPInv {
    type Public = (AtomicBool, PCell<i32>, Id, Id);

    #[logic(inline)]
    fn public(self) -> Self::Public {
        (*self.flag_perm.ward(), *self.data, self.tok_write.id(), self.tok_read.id())
    }

    #[logic(inline)]
    fn protocol(self) -> bool {
        pearlite! {
            forall<t> match self.flag_perm.val().lookup(t) {
                Some((true, view)) => {
                    self.tok_write.val() == Some(Excl(())) &&
                    match self.at_view {
                        Some(at_view) => {
                            *self.data == *at_view.val().ward() &&
                            at_view.val().val() == 42_i32 &&
                            at_view.view() <= view
                        },
                        None => self.tok_read.val() == Some(Excl(()))
                    }
                },
                _ => true,
            }
        }
    }
}

pub fn message_passing() {
    let (flag, flag_perm) = AtomicBool::new(false, SyncView::new().borrow_mut());
    let (data, mut data_perm) = PCell::new(0i32);
    let excl_write = Resource::alloc(snapshot!(Some(Excl(()))));
    let excl_read = Resource::alloc(snapshot!(Some(Excl(()))));

    let inv = AtomicInvariant::new(
        ghost!(MPInv {
            flag_perm: flag_perm.into_inner(),
            at_view: None,
            tok_write: Resource::new_unit(excl_write.id()),
            tok_read: Resource::new_unit(excl_read.id()),
            data: snapshot!(data),
        }),
        snapshot!(MESSAGE_PASSING()),
    );

    thread::scope(|s| {
        let inv: Ghost<&_> = inv.borrow();
        let data = &data;
        let flag = &flag;

        let t1 = s.spawn(move |tokens: Ghost<Tokens>| {
            let mut excl = ghost!(excl_write.into_inner());

            unsafe { *data.borrow_mut(ghost!(&mut *data_perm)) = 1 }

            flag.store(
                true,
                ghost! { |c: &mut Committer<_, _, _, Release>| {
                    inv.open(tokens.into_inner(), |inv: &mut MPInv| {
                        excl.valid_op_lemma(&inv.tok_write);
                        std::mem::swap(&mut inv.tok_write, &mut *excl);

                        let (mut sync_view, at_view) = AtView::new(ghost!(data_perm.into_inner())).into_inner();
                        inv.at_view = Some(at_view);
                        c.shoot_store(&mut inv.flag_perm, &mut sync_view);
                    })
                }},
            );
        });

        let t2 = s.spawn(move |mut tokens: Ghost<Tokens>| {
            let mut excl = ghost!(excl_read.into_inner());
            let excl_snap = snapshot!(excl);
            let mut data_perm = ghost!(None);

            #[invariant(excl == *excl_snap)]
            #[invariant(tokens.contains(MESSAGE_PASSING()))]
            while !flag.load(ghost! { |c: &Committer<_, bool, Acquire, _>| {
            inv.open(tokens.reborrow(), |inv: &mut MPInv| {
                if !c.val_load() {
                    return
                }
                let mut sync_view = *SyncView::new();
                c.shoot_load(&inv.flag_perm, &mut sync_view);

                excl.valid_op_lemma(&inv.tok_read);

                swap(&mut inv.tok_read, &mut *excl);
                *data_perm = Some(inv.at_view.take().unwrap().sync(sync_view))
            })}}) {}

            let res = unsafe { data.get(ghost! { data_perm.as_ref().unwrap() }) };
            proof_assert!(res == 1i32)
        });

        let _ = t1.join_unwrap();
        let _ = t2.join_unwrap();
    });
}
