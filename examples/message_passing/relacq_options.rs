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
            view::{AtView, SyncView},
        },
        thread::{self, JoinHandleExt},
    },
};

declare_namespace! { MESSAGE_PASSING }

struct MessagePassingAtomicInv {
    atomic_own: Perm<AtomicBool>,
    at_view: Option<AtView<Perm<PermCell<i32>>>>,
    tok_write: Resource<Option<Excl<()>>>,
    tok_read: Resource<Option<Excl<()>>>,
    data: Snapshot<PermCell<i32>>,
}

impl Protocol for MessagePassingAtomicInv {
    type Public = (AtomicBool, PermCell<i32>, Id, Id);

    #[logic(inline)]
    fn public(self) -> Self::Public {
        (*self.atomic_own.ward(), *self.data, self.tok_write.id(), self.tok_read.id())
    }

    #[logic(inline)]
    fn protocol(self) -> bool {
        pearlite! {
            forall<t> match self.atomic_own.val().get(t) {
                Some((b, view)) =>
                    !b ||
                    b &&
                    self.tok_write.val() == Some(Excl(())) &&
                        match self.at_view {
                            Some(at_view) => *self.data == *at_view.val().ward() && at_view.val().val()@ == 1 && at_view.view() <= view,
                            None => self.tok_read.val() == Some(Excl(()))
                        },
                None => true
            }
        }
    }
}

pub fn message_passing() {
    let (atomic, atomic_own) = AtomicBool::new(false, SyncView::new().borrow_mut());
    let (data, mut data_own) = PermCell::new(0i32);
    let excl_write = Resource::alloc(snapshot!(Some(Excl(()))));
    let excl_read = Resource::alloc(snapshot!(Some(Excl(()))));

    let inv = AtomicInvariant::new(
        ghost!(MessagePassingAtomicInv {
            atomic_own: atomic_own.into_inner(),
            at_view: None,
            tok_write: Resource::new_unit(excl_write.id_ghost()),
            tok_read: Resource::new_unit(excl_read.id_ghost()),
            data: snapshot!(data),
        }),
        snapshot!(MESSAGE_PASSING()),
    );

    thread::scope(|s| {
        let inv: Ghost<&_> = inv.borrow();
        let data = &data;
        let atomic = &atomic;

        let t1 = s.spawn(move |tokens: Ghost<Tokens>| {
            let mut excl = ghost!(excl_write.into_inner());

            unsafe { *data.borrow_mut(ghost!(&mut *data_own)) = 1 }

            atomic.store(
                true,
                ghost! { |c: &mut Committer<_, _, _, Ordering::Release>| {
                    inv.open(tokens.into_inner(), |inv: &mut MessagePassingAtomicInv| {
                        excl.valid_op_lemma(&inv.tok_write);
                        std::mem::swap(&mut inv.tok_write, &mut *excl);

                        let (mut sync_view, at_view) = AtView::new(ghost!(data_own.into_inner())).into_inner();
                        inv.at_view = Some(at_view);
                        c.shoot_store(&mut inv.atomic_own, &mut sync_view);
                    })
                }},
            );
        });

        let t2 = s.spawn(move |mut tokens: Ghost<Tokens>| {
            let mut excl = ghost!(excl_read.into_inner());
            let excl_snap = snapshot!(excl);
            let mut data_own = ghost!(None);

            #[invariant(excl == *excl_snap)]
            #[invariant(tokens.contains(MESSAGE_PASSING()))]
            while !atomic.load(ghost! { |c: &Committer<_, bool, Ordering::Acquire, _>| {
            inv.open(tokens.reborrow(), |inv: &mut MessagePassingAtomicInv| {
                if !*snapshot!(c.val_load()).into_ghost() {
                    return
                }

                excl.valid_op_lemma(&inv.tok_read);
                std::mem::swap(&mut inv.tok_read, &mut *excl);

                let mut sync_view = *SyncView::new();
                c.shoot_load(&inv.atomic_own, &mut sync_view);
                data_own = Ghost::new(Some(inv.at_view.take().unwrap().sync(sync_view)))
            })}}) {}

            let res = unsafe { data.get(ghost! { data_own.as_ref().unwrap() }) };
            proof_assert!(res == 1i32)
        });

        let _ = t1.join_unwrap();
        let _ = t2.join_unwrap();
    });
}
