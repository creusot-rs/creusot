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
            atomic::{AtomicBool, fence_acquire, fence_release, ordering::Relaxed},
            committer::Committer,
            view::{AtView, SyncView},
        },
        thread::{self, JoinHandleExt},
    },
};

declare_namespace! { MESSAGE_PASSING }

struct MessagePassingAtomicInv {
    atomic_own: Perm<AtomicBool>,
    data_perm: Option<AtView<Perm<PCell<i32>>>>,
    tok_write: Resource<Option<Excl<()>>>,
    tok_read: Resource<Option<Excl<()>>>,
    data: Snapshot<PCell<i32>>,
}

impl Protocol for MessagePassingAtomicInv {
    type Public = (AtomicBool, PCell<i32>, Id, Id);

    #[logic(inline)]
    fn public(self) -> Self::Public {
        (*self.atomic_own.ward(), *self.data, self.tok_write.id(), self.tok_read.id())
    }

    #[logic(inline)]
    fn protocol(self) -> bool {
        pearlite! {
            forall<t> match self.atomic_own.val().lookup(t) {
                Some((b, view)) =>
                    !b ||
                    b &&
                    self.tok_write.val() == Some(Excl(())) &&
                        match self.data_perm {
                            Some(data_perm) => *self.data == *data_perm.val().ward() && data_perm.val().val()@ == 1 && data_perm.view() <= view,
                            None => self.tok_read.val() == Some(Excl(()))
                        },
                None => true
            }
        }
    }
}

pub fn message_passing() {
    let (atomic, atomic_own) = AtomicBool::new(false, SyncView::new().borrow_mut());
    let (data, mut data_own) = PCell::new(0i32);
    let excl_write = Resource::alloc(snapshot!(Some(Excl(()))));
    let excl_read = Resource::alloc(snapshot!(Some(Excl(()))));

    let inv = AtomicInvariant::new(
        ghost!(MessagePassingAtomicInv {
            atomic_own: atomic_own.into_inner(),
            data_perm: None,
            tok_write: Resource::new_unit(excl_write.id()),
            tok_read: Resource::new_unit(excl_read.id()),
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

            let (mut sync_view, data_perm) = AtView::new(ghost!(data_own.into_inner())).split();
            let rel_view = fence_release(sync_view);

            atomic.store(
                true,
                ghost! { |c: &mut Committer<_, _, _, Relaxed>| {
                    inv.open(tokens.into_inner(), |inv: &mut MessagePassingAtomicInv| {
                        excl.valid_op_lemma(&inv.tok_write);
                        std::mem::swap(&mut inv.tok_write, &mut *excl);

                        inv.data_perm = Some(data_perm.into_inner());
                        c.shoot_store(&mut inv.atomic_own, &mut sync_view, rel_view.into_inner());
                    })
                }},
            );
        });

        let t2 = s.spawn(move |mut tokens: Ghost<Tokens>| {
            let mut excl = ghost!(excl_read.into_inner());
            let excl_snap = snapshot!(excl);
            let mut data_acq_view = ghost!(None);
            let mut data_perm = ghost!(None);

            #[invariant(excl == *excl_snap)]
            #[invariant(tokens.contains(MESSAGE_PASSING()))]
            while !atomic.load(ghost! { |c: &Committer<_, bool, Relaxed, _>| {
            inv.open(tokens.reborrow(), |inv: &mut MessagePassingAtomicInv| {
                if !c.val_load() {
                    return
                }

                excl.valid_op_lemma(&inv.tok_read);
                std::mem::swap(&mut inv.tok_read, &mut *excl);

                let mut sync_view = *SyncView::new();
                let acq_view = c.shoot_load(&inv.atomic_own, &mut sync_view);

                *data_acq_view = Some(acq_view);
                *data_perm = Some(inv.data_perm.take().unwrap());
            })}}) {}

            let sync_view = fence_acquire(ghost!(data_acq_view.unwrap()));
            let data_own = ghost!(data_perm.into_inner().unwrap().sync(*sync_view));

            let res = unsafe { data.get(ghost!(&*data_own)) };
            proof_assert!(res == 1i32)
        });

        let _ = t1.join_unwrap();
        let _ = t2.join_unwrap();
    });
}
