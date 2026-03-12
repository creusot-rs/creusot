extern crate creusot_std;

use creusot_std::{
    cell::PermCell,
    ghost::{
        invariant::{AtomicInvariantSC, Protocol, Tokens, declare_namespace},
        perm::Perm,
        resource::Resource,
    },
    logic::{Id, ra::excl::Excl},
    prelude::*,
    std::{
        sync::atomic_sc::{AtomicI32, LoadCommitter, StoreCommitter},
        thread::{self, JoinHandleExt},
    },
};

declare_namespace! { MESSAGE_PASSING }

struct MessagePassingAtomicInv {
    atomic_own: Box<Perm<AtomicI32>>,
    data_own: Option<Box<Perm<PermCell<i32>>>>,
    tok: Resource<Option<Excl<()>>>,
}

impl Protocol for MessagePassingAtomicInv {
    type Public = (AtomicI32, PermCell<i32>, Id);

    #[logic(inline)]
    fn protocol(self, data: Self::Public) -> bool {
        pearlite! {
            data.0 == *self.atomic_own.ward() && data.2 == self.tok.id() &&
            (self.atomic_own.val()@ == 0 ||
             match self.data_own {
                Some(data_own) => data.1 == *data_own.ward() && self.atomic_own.val()@ == 1 && data_own.val()@ == 1,
                None => self.tok.val() == Some(Excl(())),
            })
        }
    }
}

pub fn message_passing() {
    let (atomic, atomic_own) = AtomicI32::new(0i32);
    let (data, mut data_own) = PermCell::new(0i32);
    let mut excl = Resource::alloc(snapshot!(Some(Excl(()))));

    // Initialize our invariant
    let inv = AtomicInvariantSC::new(
        ghost!(MessagePassingAtomicInv {
            atomic_own: atomic_own.into_inner(),
            data_own: None,
            tok: Resource::new_unit(excl.id_ghost())
        }),
        snapshot!((atomic, data, excl.id())),
        snapshot!(MESSAGE_PASSING()),
    );

    thread::scope(|s| {
        let inv: Ghost<&_> = inv.borrow();
        let data = &data;
        let atomic = &atomic;

        let t1 = s.spawn(move |tokens: Ghost<Tokens>| {
            unsafe { *data.borrow_mut(ghost!(&mut **data_own)) = 1 }

            atomic.store(
                1,
                ghost! { |c: &mut StoreCommitter<_>| {
                    inv.open(tokens.into_inner(), |inv: &mut MessagePassingAtomicInv| {
                        inv.data_own = Some(data_own.into_inner());
                        c.shoot(&mut inv.atomic_own);
                    })
                }},
            );
        });

        let t2 = s.spawn(move |mut tokens: Ghost<Tokens>| {
            let excl_snap = snapshot!(excl);
            let mut data_own = ghost!(None);

            #[invariant(excl == *excl_snap)]
            #[invariant(tokens.contains(MESSAGE_PASSING()))]
            while atomic.load(ghost! { |c: &mut LoadCommitter<AtomicI32>| {
            inv.open(tokens.reborrow(), |inv: &mut MessagePassingAtomicInv| {
                excl.valid_op_lemma(&inv.tok);
                if snapshot!{ c.val() }.into_ghost().into_inner() == 1 {
                    std::mem::swap(&mut inv.tok, &mut *excl);
                }
                c.shoot(&mut inv.atomic_own);
                data_own = Ghost::new(inv.data_own.take())
            })}})
                != 1
            {}

            let res = unsafe { data.get(ghost! { data_own.as_ref().unwrap() }) };
            proof_assert!(res == 1i32);
        });

        let _ = t1.join_unwrap();
        let _ = t2.join_unwrap();
    });
}
