// DEPTH 10

use creusot_std::{
    cell::PermCell,
    ghost::{
        invariant::{AtomicInvariant, Protocol, Tokens, declare_namespace},
        lifetime_logic::{EndBorrow, FullBorrow, Lifetime, LifetimeToken},
        perm::Perm,
        resource::{Authority, Resource},
    },
    invariant::Guarded,
    logic::{
        FMap, Id, Mapping,
        ra::{RA, auth::CancelLocalUpdateUnit, excl::Excl},
        real::PositiveReal,
    },
    prelude::*,
    std::sync::{
        atomic::{
            AtomicU32,
            ordering::{Acquire, Relaxed, Release},
        },
        committer::Committer,
        view::{AtView, HasTimestamp, ReleaseSyncView, SyncView, Timestamp},
    },
};

declare_namespace! { TICKET_LOCK }

struct TicketLockInv<T> {
    cell: Snapshot<PermCell<T>>,
    lft: Snapshot<Lifetime>,
    perm: Option<AtView<Guarded<FullBorrow<Perm<PermCell<T>>>>>>,
    perm_next_ticket: Perm<AtomicU32>,
    perm_now_serving: Perm<AtomicU32>,
    auth_tickets: Authority<FMap<Int, Excl<()>>>,
    inv: Snapshot<Mapping<T, bool>>,
    ts_next_ticket: Timestamp,
    ts_now_serving: Option<Timestamp>,
    token: Resource<Option<Excl<()>>>,
}

impl<T> TicketLockInv<T> {
    #[logic]
    fn next_ticket(self) -> Int {
        pearlite! { self.perm_next_ticket.val()[self.ts_next_ticket].0@ }
    }
}

impl<T> Protocol for TicketLockInv<T> {
    type Public = ((PermCell<T>, AtomicU32, AtomicU32, Lifetime, Mapping<T, bool>), Id, Id);

    #[logic]
    fn public(self) -> Self::Public {
        (
            (
                *self.cell,
                *self.perm_next_ticket.ward(),
                *self.perm_now_serving.ward(),
                *self.lft,
                *self.inv,
            ),
            self.auth_tickets.id(),
            self.token.id(),
        )
    }

    #[logic(inline)]
    fn protocol(self) -> bool {
        pearlite! {
            (forall<ts: Timestamp> self.perm_next_ticket.val().contains(ts) ==>
                self.perm_next_ticket.val().contains(ts+1) || ts == self.ts_next_ticket) &&
            (forall<k: Int> self.auth_tickets@.contains(k) ==> k < self.next_ticket())&&

            (forall<ts: Timestamp> Some(ts) != self.ts_now_serving ==>
                match self.perm_now_serving.val().get(ts) {
                    Some((n, _)) => !self.auth_tickets@.contains(n@) && n@ < self.next_ticket(),
                    None => true
                }) &&
            match (self.perm, self.ts_now_serving) {
                (Some(bor), Some(ts)) => {
                    bor.view() <= self.perm_now_serving.val()[ts].1 &&
                    bor.val().inner.lft() == *self.lft &&
                    bor.val().guard() == (|b: FullBorrow<Perm<_>>| *b.cur().ward() == *self.cell) &&
                    self.inv.get(bor.val().inner.cur().val()) &&
                    self.token@ == Some(Excl(()))
                }
                (None, None) => true,
                _ => false
            }
        }
    }
}

pub struct TicketLock<T> {
    next_ticket: AtomicU32,
    now_serving: AtomicU32,
    data: PermCell<T>,
    lft_tok: Ghost<LifetimeToken>,
    end: Ghost<EndBorrow<Perm<PermCell<T>>>>,
    inner_inv: Ghost<AtomicInvariant<TicketLockInv<T>>>,
    pub inv: Snapshot<Mapping<T, bool>>,
}

impl<T> Invariant for TicketLock<T> {
    #[logic(prophetic, inline)]
    fn invariant(self) -> bool {
        pearlite! {
            self.inner_inv.public().0 == (self.data, self.next_ticket, self.now_serving, self.lft_tok.lft(), *self.inv) &&
            self.lft_tok.frac() == PositiveReal::from_int(1) &&
            self.end.lft() == self.lft_tok.lft() &&
            *(^self.end).ward() == self.data &&
            self.inner_inv.namespace() == TICKET_LOCK()
        }
    }
}

pub struct TicketLockGuard<'a, T> {
    lock: &'a TicketLock<T>,
    perm: Ghost<Guarded<FullBorrow<Perm<PermCell<T>>>>>,
    token: Ghost<Resource<Option<Excl<()>>>>,
    pub inv: Snapshot<Mapping<T, bool>>,
}

impl<'a, T> View for TicketLockGuard<'a, T> {
    type ViewTy = T;

    #[logic]
    fn view(self) -> T {
        self.perm.inner.cur().val()
    }
}

impl<'a, T> Invariant for TicketLockGuard<'a, T> {
    #[logic(inline)]
    fn invariant(self) -> bool {
        pearlite! {
            self.perm.guard() == (|b: FullBorrow<Perm<_>>| *b.cur().ward() == self.lock.data) &&
            self.perm.inner.lft() == self.lock.lft_tok.lft() &&
            self.inv == self.lock.inv &&
            self.token.id() == self.lock.inner_inv.public().2 &&
            self.token@ == Some(Excl(()))
        }
    }
}

impl<T> TicketLock<T> {
    #[requires(inv.get(data))]
    #[ensures(result.inv == inv)]
    pub fn new(data: T, inv: Snapshot<Mapping<T, bool>>) -> Self {
        let mut view_next_ticket = SyncView::new();
        let (next_ticket, perm_next_ticket) = AtomicU32::new(0, ghost!(&mut view_next_ticket));
        let (data, perm_data) = PermCell::new(data);
        let lft_tok = ghost!(LifetimeToken::new());
        let (bor, end) = FullBorrow::new(perm_data, snapshot!(lft_tok.lft()));
        let bor = ghost!(bor.into_inner().add_guard(snapshot!(|p: Perm<_>| *p.ward() == data)));
        let (mut view, perm) = AtView::new(bor).split();
        let (now_serving, perm_now_serving) = AtomicU32::new(0, ghost!(&mut *view));
        let inner_inv = AtomicInvariant::new(
            ghost!(TicketLockInv {
                cell: snapshot!(data),
                lft: snapshot!(lft_tok.lft()),
                perm: Some(perm.into_inner()),
                perm_next_ticket: perm_next_ticket.into_inner(),
                perm_now_serving: perm_now_serving.into_inner(),
                auth_tickets: Authority::alloc().into_inner(),
                ts_now_serving: Some(*snapshot!(now_serving.get_timestamp(*view)).into_ghost()),
                ts_next_ticket: *snapshot!(next_ticket.get_timestamp(*view_next_ticket))
                    .into_ghost(),
                token: Resource::alloc(snapshot!(Some(Excl(())))).into_inner(),
                inv
            }),
            snapshot!(TICKET_LOCK()),
        );
        TicketLock { next_ticket, now_serving, data, lft_tok, end, inner_inv, inv }
    }

    #[requires(tokens.contains(TICKET_LOCK()))]
    #[ensures(self.inv.get(result@))]
    #[ensures(result.inv == self.inv)]
    pub fn lock<'a, 'b>(&'a self, mut tokens: Ghost<Tokens<'b>>) -> TicketLockGuard<'a, T> {
        let mut ticket_own = ghost!(None);

        let ticket = self.next_ticket.fetch_add::<_, Relaxed>(
            1,
            ghost! { |c: &mut Committer<_, _, Relaxed, Relaxed>| {
                #[trusted]
                proof_assert!(c.val_load() < u32::MAX);
                self.inner_inv.open(tokens.reborrow(), |inv: &mut TicketLockInv<T>| {
                    c.shoot_load(&inv.perm_next_ticket, &mut *SyncView::new());
                    c.shoot_store(&mut inv.perm_next_ticket, &mut *SyncView::new(), *ReleaseSyncView::new());
                    proof_assert!(c.timestamp() == inv.ts_next_ticket);
                    inv.ts_next_ticket += 1int;
                    *ticket_own = Some(inv.auth_tickets.add_fragment(snapshot!(FMap::singleton(c.val_load()@, Excl(())))));
                })
            }},
        );

        let mut perm = ghost!(None);
        let mut token =
            ghost!(Resource::new_unit(*snapshot!(self.inner_inv.public().2).into_ghost()));

        #[invariant(tokens.contains(TICKET_LOCK()))]
        #[invariant(*ticket_own != None)]
        #[invariant(ticket_own.unwrap_logic().id() == self.inner_inv.public().1)]
        #[invariant(ticket_own.unwrap_logic()@.get(ticket@) == Some(Excl(())))]
        #[invariant(token.id() == self.inner_inv.public().2 )]
        while self.now_serving.load(ghost!(|c: &Committer<_, _, Acquire, _>| {
            self.inner_inv.open(tokens.reborrow(), |inv: &mut TicketLockInv<T>| {
                if *snapshot!(c.val_load() != ticket).into_ghost() {
                    return;
                }
                let mut view = SyncView::new();
                c.shoot_load(&inv.perm_now_serving, &mut *view);
                let auth_tickets_snap = snapshot!(inv.auth_tickets);
                inv.auth_tickets.update(ticket_own.as_mut().unwrap(), CancelLocalUpdateUnit);
                proof_assert!(exists<m> inv.auth_tickets@.op(m) == Some(auth_tickets_snap@));
                proof_assert!(forall<k> inv.auth_tickets@.contains(k) ==> auth_tickets_snap@.contains(k) && k != ticket@);
                inv.ts_now_serving = None;
                *perm = Some(inv.perm.take().unwrap().sync(*view));
                std::mem::swap(&mut inv.token, &mut *token);
            })
        })) != ticket
        {}

        TicketLockGuard {
            lock: self,
            perm: ghost!(perm.into_inner().unwrap()),
            inv: self.inv,
            token,
        }
    }

    pub fn into_inner(self) -> T {
        let perm = ghost! {
            let dead = self.lft_tok.into_inner().end();
            self.end.into_inner().get(dead)
        };
        self.data.into_inner(perm)
    }
}

impl<'a, T> TicketLockGuard<'a, T> {
    #[ensures(*result == self@)]
    pub fn deref(&self) -> &T {
        unsafe { self.lock.data.borrow(ghost!(self.perm.inner.borrow(&self.lock.lft_tok))) }
    }

    #[ensures(*result == self@ && ^result == (^self)@)]
    #[ensures((*self).inv == (^self).inv)]
    pub fn deref_mut(&mut self) -> &mut T {
        ghost_let!(p = &mut self.perm.inner);
        unsafe { self.lock.data.borrow_mut(ghost!(p.into_inner().borrow_mut(&self.lock.lft_tok))) }
    }

    #[requires(tokens.contains(TICKET_LOCK()))]
    #[requires(self.inv.get(self@))]
    pub fn unlock(mut self, mut tokens: Ghost<Tokens>) {
        let ticket = self.lock.now_serving.load::<_, Relaxed>(ghost!(|_: &_| {}));
        self.lock.now_serving.store(
            ticket.wrapping_add(1),
            ghost!(|c: &mut Committer<_, _, _, Release>| {
                self.lock.inner_inv.open(tokens.into_inner(), |inv: &mut TicketLockInv<T>| {
                    let (mut view, perm) = AtView::new(self.perm).into_inner();
                    c.shoot_store(&mut inv.perm_now_serving, &mut view);
                    inv.token.valid_op_lemma(&self.token);
                    std::mem::swap(&mut inv.token, &mut self.token);

                    inv.perm = Some(perm);
                    inv.ts_now_serving = Some(*snapshot!(c.timestamp() + 1).into_ghost());
                })
            }),
        );
    }
}
