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
        sync::atomic_relacq::{AtomicI32, LoadCommitter, StoreCommitter},
        thread::{self, JoinHandleExt},
    },
    sync_view::{AtView, SyncView},
};

declare_namespace! { MESSAGE_PASSING }

struct MessagePassingAtomicInv {
    atomic_own: Box<Perm<AtomicI32>>,
    at_view: Option<AtView<Box<Perm<PermCell<i32>>>>>,
    tok_write: Resource<Option<Excl<()>>>,
    tok_read: Resource<Option<Excl<()>>>,
}

impl Protocol for MessagePassingAtomicInv {
    type Public = (AtomicI32, PermCell<i32>, Id, Id);

    #[logic(inline)]
    fn protocol(self, data: Self::Public) -> bool {
        pearlite! {
            let (atomic, perm, excl_write, excl_read) = data;
            atomic == *self.atomic_own.ward() && excl_write == self.tok_write.id() && excl_read == self.tok_read.id() &&
            forall<t> match self.atomic_own.val().get(t) {
                Some((v, view)) =>
                    v == 0i32 ||
                    v == 1i32 &&
                    self.tok_write.val() == Some(Excl(())) &&
                        match self.at_view {
                            Some(at_view) => perm == *at_view.val().ward() && at_view.val().val()@ == 1 && at_view.view_logic().le_log(view),
                            None => self.tok_read.val() == Some(Excl(()))
                        },
                None => true
            }
        }
    }
}

pub fn message_passing() {
    let (atomic, atomic_own) = AtomicI32::new(0i32, SyncView::new().borrow_mut());
    let (data, mut data_own) = PermCell::new(0i32);
    let excl_write = Resource::alloc(snapshot!(Some(Excl(()))));
    let excl_read = Resource::alloc(snapshot!(Some(Excl(()))));

    let inv = AtomicInvariant::new(
        ghost!(MessagePassingAtomicInv {
            atomic_own: atomic_own.into_inner(),
            at_view: None,
            tok_write: Resource::new_unit(excl_write.id_ghost()),
            tok_read: Resource::new_unit(excl_read.id_ghost())
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

            unsafe {
                *data.borrow_mut(ghost!(&mut **data_own)) = 1;
            }

            atomic.store(
                1,
                ghost! { |c: &mut StoreCommitter<_, _>| {
                    inv.open(tokens.into_inner(), |inv: &mut MessagePassingAtomicInv| {
                        let (mut sync_view, at_view) = AtView::new(ghost!(data_own.into_inner())).into_inner();
                        excl.valid_op_lemma(&inv.tok_write);
                        std::mem::swap(&mut inv.tok_write, &mut *excl);
                        inv.at_view = Some(at_view);
                        c.shoot(&mut inv.atomic_own, &mut sync_view);
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
            while atomic.load(ghost! { |c: &mut LoadCommitter<i32, _>| {
            inv.open(tokens.reborrow(), |inv: &mut MessagePassingAtomicInv| {
                excl.valid_op_lemma(&inv.tok_read);
                let value = snapshot!{ c.val() }.into_ghost().into_inner();
                let mut sync_view = *SyncView::new();
                c.shoot(&inv.atomic_own, &mut sync_view);
                if value == 1 {
                    std::mem::swap(&mut inv.tok_read, &mut *excl);
                    data_own = Ghost::new(Some(inv.at_view.take().unwrap().into_inner(sync_view)))
                }
            })}})
                != 1
            {}
            let res = unsafe { data.get(ghost! { data_own.as_ref().unwrap() }) };
            proof_assert!(res == 1i32)
        });

        let _ = t1.join_unwrap();
        let _ = t2.join_unwrap();
    });
}
