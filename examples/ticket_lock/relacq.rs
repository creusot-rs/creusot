// DEPTH 10

use core::sync::atomic::Ordering;

use creusot_std::{
    cell::PCell,
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

type UpdateCommitter = Committer<AtomicU32, u32, Relaxed, Relaxed>;
type LoadCommitter = Committer<AtomicU32, u32, Acquire, ()>;
type StoreCommitter = Committer<AtomicU32, u32, (), Release>;

struct TicketLockInv<T> {
    cell: Snapshot<PCell<T>>,
    lft: Snapshot<Lifetime>,
    data_perm: Option<AtView<Guarded<FullBorrow<Perm<PCell<T>>>, PCell<T>>>>,
    next_ticket_perm: Perm<AtomicU32>,
    now_serving_perm: Perm<AtomicU32>,
    auth_tickets: Authority<FMap<Int, Excl<()>>>,
    inv: Snapshot<Mapping<T, bool>>,
    ts_next_ticket: Timestamp,
    ts_now_serving: Option<Timestamp>,
    token: Resource<Option<Excl<()>>>,
}

impl<T> TicketLockInv<T> {
    #[logic]
    fn next_ticket(self) -> Int {
        pearlite! { self.next_ticket_perm.val()[self.ts_next_ticket].0@ }
    }
}

impl<T> Protocol for TicketLockInv<T> {
    type Public = ((PCell<T>, AtomicU32, AtomicU32, Lifetime, Mapping<T, bool>), Id, Id);

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
            self.token.id(),
        )
    }

    #[logic(inline)]
    fn protocol(self) -> bool {
        pearlite! {
            let ((cell, _, _, lft, inv), _, _) = self.public();

            (forall<ts: Timestamp> self.next_ticket_perm.val().contains(&ts) ==>
                self.next_ticket_perm.val().contains_logic(ts+1) || ts == self.ts_next_ticket) &&
            (forall<k: Int> self.auth_tickets@.contains(&k) ==> k < self.next_ticket()) &&

            (forall<ts: Timestamp> Some(ts) != self.ts_now_serving ==>
                match self.now_serving_perm.val().lookup(ts) {
                    Some((n, _)) => !self.auth_tickets@.contains(&n@) && n@ < self.next_ticket(),
                    None => true
                }) &&
            match (self.data_perm, self.ts_now_serving) {
                (Some(bor), Some(ts)) => {
                    bor.view() <= self.now_serving_perm.val()[ts].1 &&
                    bor.val().inner.lft() == lft &&
                    bor.val().guard() == cell &&
                    inv.get(bor.val().inner.cur().val()) &&
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
    data: PCell<T>,
    lft_tok: Ghost<LifetimeToken>,
    end: Ghost<EndBorrow<Perm<PCell<T>>>>,
    inner_inv: Ghost<AtomicInvariant<TicketLockInv<T>>>,
    pub inv: Snapshot<Mapping<T, bool>>,
}

impl<T> Invariant for TicketLock<T> {
    #[logic(prophetic, inline)]
    fn invariant(self) -> bool {
        pearlite! {
            let (public, _, _) = self.inner_inv.public();

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
    token: Ghost<Resource<Option<Excl<()>>>>,
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
            let (_, _, id) = self.lock.inner_inv.public();

            self.data_perm.guard() == self.lock.data
                && self.data_perm.inner.lft() == self.lock.lft_tok.lft()
                && self.inv == self.lock.inv
                && self.token.id() == id
                && self.token@ == Some(Excl(()))
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
        let bor = ghost!(bor.into_inner().into_inner().add_guard(snapshot!(data)));
        let end = ghost!(end.into_inner().into_inner());

        let mut view_next_ticket = ghost!(SyncView::new().into_inner());
        let (next_ticket, next_ticket_perm) = AtomicU32::new(0, ghost!(&mut view_next_ticket));

        let (mut view, data_perm) = ghost!(AtView::new(bor).into_inner()).split();
        let (now_serving, now_serving_perm) = AtomicU32::new(0, ghost!(&mut *view));

        let inner_inv = ghost!(
            AtomicInvariant::new(
                ghost!(TicketLockInv {
                    cell: snapshot!(data),
                    lft: snapshot!(lft_tok.lft()),
                    data_perm: Some(data_perm.into_inner()),
                    next_ticket_perm: next_ticket_perm.into_inner(),
                    now_serving_perm: now_serving_perm.into_inner(),
                    auth_tickets: Authority::alloc().into_inner(),
                    ts_now_serving: Some(*snapshot!(now_serving.get_timestamp(*view)).into_ghost()),
                    ts_next_ticket: *snapshot!(next_ticket.get_timestamp(*view_next_ticket))
                        .into_ghost(),
                    token: Resource::alloc(snapshot!(Some(Excl(())))).into_inner(),
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

        let ticket = self.next_ticket.fetch_add::<_, Relaxed>(
            1,
            Ordering::Relaxed,
            ghost! { |c: &mut UpdateCommitter| {
                #[trusted]
                proof_assert!(c.val_load() < u32::MAX);
                self.inner_inv.open(tokens.reborrow(), |inner_inv: &mut TicketLockInv<T>| {
                    c.shoot_load(&inner_inv.next_ticket_perm, &mut *SyncView::new());
                    c.shoot_store(&mut inner_inv.next_ticket_perm, &mut *SyncView::new(), *ReleaseSyncView::new());
                    proof_assert!(c.timestamp() == inner_inv.ts_next_ticket);
                    inner_inv.ts_next_ticket += 1int;
                    *ticket_own = Some(inner_inv.auth_tickets.add_fragment(snapshot!(FMap::singleton(c.val_load()@, Excl(())))));
                })
            }},
        );

        let mut data_perm = ghost!(None);
        let mut token =
            ghost!(Resource::new_unit(*snapshot!(self.inner_inv.public().2).into_ghost()));

        #[invariant(tokens.contains(TICKET_LOCK()))]
        #[invariant(*ticket_own != None)]
        #[invariant(ticket_own.unwrap_logic().id() == self.inner_inv.public().1)]
        #[invariant(ticket_own.unwrap_logic()@.lookup(ticket@) == Some(Excl(())))]
        #[invariant(token.id() == self.inner_inv.public().2)]
        while self.now_serving.load(Ordering::Acquire, ghost! { |c: &LoadCommitter| {
            self.inner_inv.open(tokens.reborrow(), |inner_inv: &mut TicketLockInv<T>| {
                if c.val_load() != ticket {
                    return;
                }
                let mut view = SyncView::new();
                c.shoot_load(&inner_inv.now_serving_perm, &mut *view);
                let auth_tickets_snap = snapshot!(inner_inv.auth_tickets);
                inner_inv.auth_tickets.update(ticket_own.as_mut().unwrap(), CancelLocalUpdateUnit);
                proof_assert!(exists<m> inner_inv.auth_tickets@.op(m) == Some(auth_tickets_snap@));
                proof_assert!(forall<k> inner_inv.auth_tickets@.contains(&k) ==> auth_tickets_snap@.contains(&k) && k != ticket@);
                proof_assert!(auth_tickets_snap@.contains(&ticket@));
                inner_inv.ts_now_serving = None;
                *data_perm = Some(inner_inv.data_perm.take().unwrap().sync(*view));
                std::mem::swap(&mut inner_inv.token, &mut *token);
            })
        }}) != ticket
        {}

        TicketLockGuard {
            lock: self,
            data_perm: ghost!(data_perm.into_inner().unwrap()),
            inv: snapshot!(self.inv.inner()),
            token,
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
    pub fn unlock(mut self, tokens: Ghost<Tokens>) {
        let ticket =
            self.lock.now_serving.load::<_, Relaxed>(Ordering::Relaxed, ghost! { |_: &_| {} });

        self.lock.now_serving.store(
            ticket.wrapping_add(1),
            Ordering::Release,
            ghost! { |c: &mut StoreCommitter| {
                self.lock.inner_inv.open(tokens.into_inner(), |inner_inv: &mut TicketLockInv<T>| {
                    let (mut view, data_perm) = AtView::new(self.data_perm).into_inner();
                    c.shoot_store(&mut inner_inv.now_serving_perm, &mut view);
                    inner_inv.token.valid_op_lemma(&self.token);
                    std::mem::swap(&mut inner_inv.token, &mut self.token);

                    inner_inv.data_perm = Some(data_perm);
                    inner_inv.ts_now_serving = Some(*snapshot!(c.timestamp() + 1).into_ghost());
                })
            }},
        );
    }
}
