use core::sync::atomic::Ordering;

use creusot_std::{
    cell::PCell,
    ghost::{
        invariant::{AtomicInvariantSC, Protocol, Tokens, declare_namespace},
        lifetime_logic::{EndBorrow, FullBorrow, Lifetime, LifetimeToken},
        perm::Perm,
        resource::Authority,
    },
    invariant::Guarded,
    logic::{
        FMap, Id, Mapping,
        ra::{RA, auth::CancelLocalUpdateUnit, excl::Excl},
        real::PositiveReal,
    },
    prelude::*,
    std::sync::{
        atomic_sc::{AtomicU32, ordering::SeqCst},
        committer::Committer,
    },
};

declare_namespace! { TICKET_LOCK }

type UpdateCommitter = Committer<AtomicU32, u32, SeqCst, SeqCst>;
type LoadCommitter = Committer<AtomicU32, u32, SeqCst, ()>;
type StoreCommitter = Committer<AtomicU32, u32, (), SeqCst>;

struct TicketLockInv<T> {
    cell: Snapshot<PCell<T>>,
    lft: Snapshot<Lifetime>,
    data_perm: Option<Guarded<FullBorrow<Perm<PCell<T>>>, PCell<T>>>,
    next_ticket_perm: Perm<AtomicU32>,
    now_serving_perm: Perm<AtomicU32>,
    auth_tickets: Authority<FMap<Int, Excl<()>>>,
    inv: Snapshot<Mapping<T, bool>>,
}

impl<T> Protocol for TicketLockInv<T> {
    type Public = ((PCell<T>, AtomicU32, AtomicU32, Lifetime, Mapping<T, bool>), Id);

    #[logic]
    fn public(self) -> Self::Public {
        (
            (
                *self.cell,
                *self.next_ticket_perm.ward(),
                *self.now_serving_perm.ward(),
                *self.lft,
                *self.inv,
            ),
            self.auth_tickets.id(),
        )
    }

    #[logic(inline)]
    fn protocol(self) -> bool {
        pearlite! {
            let ((cell, _, _, lft, inv), _) = self.public();

            (forall<k: Int> self.auth_tickets@.contains(&k) ==> k < self.next_ticket_perm.val()@) &&
            match self.data_perm {
                Some(bor) => {
                    bor.inner.lft() == lft &&
                    bor.guard() == cell &&
                    inv.get(bor.inner.cur().val())
                }
                None => {
                    let n = self.now_serving_perm.val();
                    !self.auth_tickets@.contains(&n@) && n < self.next_ticket_perm.val()
                }
            }
        }
    }
}

pub struct TicketLock<T> {
    next_ticket: AtomicU32,
    now_serving: AtomicU32,
    data: PCell<T>,
    lft_tok: Ghost<LifetimeToken>,
    end: Ghost<EndBorrow<Perm<PCell<T>>>>,
    inner_inv: Ghost<AtomicInvariantSC<TicketLockInv<T>>>,
    pub inv: Snapshot<Mapping<T, bool>>,
}

impl<T> Invariant for TicketLock<T> {
    #[logic(prophetic, inline)]
    fn invariant(self) -> bool {
        pearlite! {
            let (public, _) = self.inner_inv.public();

            public == (self.data, self.next_ticket, self.now_serving, self.lft_tok.lft(), *self.inv)
                && self.lft_tok.frac() == PositiveReal::from_int(1)
                && self.end.lft() == self.lft_tok.lft()
                && *(^self.end).ward() == self.data
                && self.inner_inv.namespace() == TICKET_LOCK()
        }
    }
}

pub struct TicketLockGuard<'a, T> {
    lock: &'a TicketLock<T>,
    data_perm: Ghost<Guarded<FullBorrow<Perm<PCell<T>>>, PCell<T>>>,
    pub inv: Snapshot<Mapping<T, bool>>,
}

impl<'a, T> View for TicketLockGuard<'a, T> {
    type ViewTy = T;

    #[logic]
    fn view(self) -> T {
        self.data_perm.inner.cur().val()
    }
}

impl<'a, T> Invariant for TicketLockGuard<'a, T> {
    #[logic(inline)]
    fn invariant(self) -> bool {
        pearlite! {
            self.data_perm.guard() == self.lock.data
                && self.data_perm.inner.lft() == self.lock.lft_tok.lft()
                && self.inv == self.lock.inv
        }
    }
}

impl<T> TicketLock<T> {
    #[requires(inv.get(data))]
    #[ensures(result.inv == inv)]
    pub fn new(data: T, inv: Snapshot<Mapping<T, bool>>) -> Self {
        let (data, data_perm) = PCell::new(data);

        let lft_tok = ghost!(LifetimeToken::new());
        let (bor, end) = ghost!(FullBorrow::new(data_perm, snapshot!(lft_tok.lft()))).split();
        let bor = ghost!(bor.into_inner().into_inner());
        let end = ghost!(end.into_inner().into_inner());

        let (next_ticket, next_ticket_perm) = AtomicU32::new(0);
        let (now_serving, now_serving_perm) = AtomicU32::new(0);

        let inner_inv = ghost!(
            AtomicInvariantSC::new(
                ghost!(TicketLockInv {
                    cell: snapshot!(data),
                    lft: snapshot!(lft_tok.lft()),
                    data_perm: Some(bor.into_inner().add_guard(snapshot!(data))),
                    next_ticket_perm: next_ticket_perm.into_inner(),
                    now_serving_perm: now_serving_perm.into_inner(),
                    auth_tickets: Authority::alloc().into_inner(),
                    inv
                }),
                snapshot!(TICKET_LOCK()),
            )
            .into_inner()
        );

        TicketLock { next_ticket, now_serving, data, lft_tok, end, inner_inv, inv }
    }

    #[requires(tokens.contains(TICKET_LOCK()))]
    #[ensures(self.inv.get(result@))]
    #[ensures(result.inv == self.inv)]
    pub fn lock<'a, 'b>(&'a self, mut tokens: Ghost<Tokens<'b>>) -> TicketLockGuard<'a, T> {
        let mut ticket_own = ghost!(None);

        let ticket = self.next_ticket.fetch_add(
            1,
            Ordering::SeqCst,
            ghost! { |c: &mut UpdateCommitter| {
                #[trusted]
                proof_assert!(c.val_load() < u32::MAX);
                self.inner_inv.open(tokens.reborrow(), |inner_inv: &mut TicketLockInv<T>| {
                    c.shoot_load(&inner_inv.next_ticket_perm);
                    c.shoot_store(&mut inner_inv.next_ticket_perm);
                    *ticket_own = Some(inner_inv.auth_tickets.add_fragment(snapshot!(FMap::singleton(c.val_load()@, Excl(())))))
                })
            }},
        );

        let mut data_perm = ghost!(None);

        #[invariant(tokens.contains(TICKET_LOCK()))]
        #[invariant(*ticket_own != None)]
        #[invariant(ticket_own.unwrap_logic().id() == self.inner_inv.public().1)]
        #[invariant(ticket_own.unwrap_logic()@.lookup(ticket@) == Some(Excl(())))]
        while self.now_serving.load(
            Ordering::SeqCst,
            ghost! { |c: &LoadCommitter| {
                self.inner_inv.open(tokens.reborrow(), |inner_inv: &mut TicketLockInv<T>| {
                    if c.val_load() != ticket {
                        return;
                    }
                    c.shoot_load(&inner_inv.now_serving_perm);
                    let auth_tickets_snap = snapshot!(inner_inv.auth_tickets);
                    inner_inv.auth_tickets.update(ticket_own.as_mut().unwrap(), CancelLocalUpdateUnit);
                    proof_assert!(exists<m> inner_inv.auth_tickets@.op(m) == Some(auth_tickets_snap@));
                    proof_assert!(forall<k> inner_inv.auth_tickets@.contains(&k) ==> auth_tickets_snap@.contains(&k) && k != ticket@);
                    proof_assert!(auth_tickets_snap@.contains(&ticket@));
                    *data_perm = inner_inv.data_perm.take();
                })
            }},
        ) != ticket
        {}

        TicketLockGuard {
            lock: self,
            data_perm: ghost!(data_perm.into_inner().unwrap()),
            inv: snapshot!(self.inv.inner()),
        }
    }

    pub fn into_inner(self) -> T {
        let data_perm = ghost! {
            let dead = self.lft_tok.into_inner().end();
            self.end.into_inner().get(dead)
        };
        self.data.into_inner(data_perm)
    }
}

impl<'a, T> TicketLockGuard<'a, T> {
    #[ensures(*result == self@)]
    pub fn deref(&self) -> &T {
        unsafe { self.lock.data.borrow(ghost!(self.data_perm.inner.borrow(&self.lock.lft_tok))) }
    }

    #[ensures(*result == self@ && ^result == (^self)@)]
    #[ensures((*self).inv == (^self).inv)]
    pub fn deref_mut(&mut self) -> &mut T {
        ghost_let!(p = &mut self.data_perm.inner);
        unsafe { self.lock.data.borrow_mut(ghost!(p.into_inner().borrow_mut(&self.lock.lft_tok))) }
    }

    #[requires(tokens.contains(TICKET_LOCK()))]
    #[requires(self.inv.get(self@))]
    pub fn unlock(self, tokens: Ghost<Tokens>) {
        let ticket = self.lock.now_serving.load(Ordering::SeqCst, ghost! { |_: &_| {} });

        self.lock.now_serving.store(
            ticket.wrapping_add(1),
            Ordering::SeqCst,
            ghost! { |c: &mut StoreCommitter| {
                self.lock.inner_inv.open(tokens.into_inner(), |inner_inv: &mut TicketLockInv<T>| {
                    c.shoot_store(&mut inner_inv.now_serving_perm);
                    inner_inv.data_perm = Some(self.data_perm.into_inner())
                })
            }},
        );
    }
}
