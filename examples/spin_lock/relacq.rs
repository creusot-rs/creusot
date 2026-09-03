use creusot_std::{
    cell::PermCell,
    ghost::{
        invariant::{AtomicInvariantSC, Protocol, Tokens, declare_namespace},
        lifetime_logic::{EndBorrow, FullBorrow, Lifetime, LifetimeToken},
        perm::Perm,
        resource::Resource,
    },
    logic::{Id, Mapping, ra::excl::Excl, real::PositiveReal},
    prelude::*,
    std::sync::{
        atomic::{AtomicBool, Ordering},
        committer::Committer,
        view::{AtView, HasTimestamp, ReleaseSyncView, SyncView, Timestamp},
    },
};

declare_namespace! { SPIN_LOCK }

struct SpinLockInv<T> {
    cell: Snapshot<PermCell<T>>,
    lft: Snapshot<Lifetime>,
    perm_atomic: Perm<AtomicBool>,
    perm: Option<AtView<FullBorrow<Perm<PermCell<T>>>>>,
    excl: Resource<Option<Excl<()>>>,
    ts: Option<Timestamp>,
    inv: Snapshot<Mapping<T, bool>>,
}

impl<T> Protocol for SpinLockInv<T> {
    type Public = ((PermCell<T>, AtomicBool, Lifetime, Mapping<T, bool>), Id);

    #[logic]
    fn public(self) -> Self::Public {
        ((*self.cell, *self.perm_atomic.ward(), *self.lft, *self.inv), self.excl.id())
    }

    #[logic]
    fn protocol(self) -> bool {
        pearlite! {
            (forall<t, view> self.perm_atomic.val().get(t) == Some((false, view)) ==>
                Some(t) == self.ts || self.perm_atomic.val().get(t + 1) != None) &&
            match (self.perm, self.ts, self.excl.val()) {
                (None, None, None) => true,
                (Some(bor), Some(ts), Some(_)) =>
                    bor.view() <= self.perm_atomic.val()[ts].1 &&
                    bor.val().lft() == *self.lft &&
                    self.inv.get(*bor.val().cur().val()) &&
                    *bor.val().cur().ward() == *self.cell,
                _ => false
            }
        }
    }
}

pub struct SpinLock<T> {
    atomic: AtomicBool,
    data: PermCell<T>,
    lft_tok: Ghost<LifetimeToken>,
    end: Ghost<EndBorrow<Perm<PermCell<T>>>>,
    inner_inv: Ghost<AtomicInvariantSC<SpinLockInv<T>>>,
    pub inv: Snapshot<Mapping<T, bool>>,
}

impl<T> Invariant for SpinLock<T> {
    #[logic]
    fn invariant(self) -> bool {
        self.inner_inv.public().0 == (self.data, self.atomic, self.lft_tok.lft(), *self.inv)
            && self.lft_tok.frac() == PositiveReal::from_int(1)
            && self.end.lft() == self.lft_tok.lft()
            && self.inner_inv.namespace() == SPIN_LOCK()
    }
}

pub struct SpinLockGuard<'a, T> {
    lock: &'a SpinLock<T>,
    perm: Ghost<FullBorrow<Perm<PermCell<T>>>>,
    excl: Ghost<Resource<Option<Excl<()>>>>,
    pub inv: Snapshot<Mapping<T, bool>>,
}

impl<'a, T> View for SpinLockGuard<'a, T> {
    type ViewTy = T;

    #[logic]
    fn view(self) -> T {
        *self.perm.cur().val()
    }
}

impl<'a, T> Invariant for SpinLockGuard<'a, T> {
    #[logic]
    fn invariant(self) -> bool {
        *self.perm.cur().ward() == self.lock.data
            && self.perm.lft() == self.lock.lft_tok.lft()
            && self.excl.val() != None
            && self.excl.id() == self.lock.inner_inv.public().1
            && self.inv == self.lock.inv
    }
}

impl<T> SpinLock<T> {
    #[requires(inv.get(data))]
    #[ensures(result.inv == inv)]
    pub fn new(data: T, inv: Snapshot<Mapping<T, bool>>) -> Self {
        let (data, perm_data) = PermCell::new(data);
        let lft_tok = ghost!(LifetimeToken::new());
        let (bor, end) = FullBorrow::new(perm_data, snapshot!(lft_tok.lft()));
        let (mut view, perm) = AtView::new(bor).split();
        let (atomic, perm_atomic) = AtomicBool::new(false, ghost!(&mut *view));
        let inner_inv = AtomicInvariantSC::new(
            ghost!(SpinLockInv {
                cell: snapshot!(data),
                lft: snapshot!(lft_tok.lft()),
                perm: Some(perm.into_inner()),
                perm_atomic: perm_atomic.into_inner(),
                excl: Resource::alloc(snapshot!(Some(Excl(())))).into_inner(),
                ts: Some(*snapshot!(atomic.get_timestamp(*view)).into_ghost()),
                inv
            }),
            snapshot!(SPIN_LOCK()),
        );
        SpinLock { atomic, data, lft_tok, end, inner_inv, inv }
    }

    #[requires(tokens.contains(SPIN_LOCK()))]
    #[ensures(self.inv.get(result@))]
    #[ensures(result.inv == self.inv)]
    pub fn lock<'a, 'b>(&'a self, mut tokens: Ghost<Tokens<'b>>) -> SpinLockGuard<'a, T> {
        let mut perm = ghost!(None);
        let mut excl = ghost!(None);

        #[invariant(tokens.contains(SPIN_LOCK()))]
        while let Err(_) =
            self.atomic.compare_exchange_weak::<_, Ordering::Acquire, Ordering::Relaxed>(
                false,
                true,
                ghost!(|c: Result<
                    &mut Committer<_, _, Ordering::Acquire, Ordering::Relaxed>,
                    &_,
                >| {
                    if let Ok(c) = c {
                        self.inner_inv.open(tokens.reborrow(), |inner_inv: &mut SpinLockInv<T>| {
                            let mut view = *SyncView::new();
                            c.shoot_load(&inner_inv.perm_atomic, &mut view);
                            c.shoot_store(
                                &mut inner_inv.perm_atomic,
                                &mut view,
                                *ReleaseSyncView::new(),
                            );
                            proof_assert!(Some(c.timestamp()) == inner_inv.ts);
                            *perm = Some(inner_inv.perm.take().unwrap().sync(view));
                            *excl = Some(
                                inner_inv
                                    .excl
                                    .split_off(snapshot!(Some(Excl(()))), snapshot!(None)),
                            );
                            inner_inv.ts = None
                        })
                    }
                }),
            )
        {}

        SpinLockGuard {
            lock: self,
            perm: ghost!(perm.into_inner().unwrap()),
            excl: ghost!(excl.into_inner().unwrap()),
            inv: self.inv,
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

impl<'a, T> SpinLockGuard<'a, T> {
    #[ensures(*result == self@)]
    pub fn deref(&self) -> &T {
        unsafe { self.lock.data.borrow(ghost!((*self.perm).borrow(&self.lock.lft_tok))) }
    }

    #[ensures(*result == self@ && ^result == (^self)@)]
    #[ensures((*self).inv == (^self).inv)]
    pub fn deref_mut(&mut self) -> &mut T {
        unsafe { self.lock.data.borrow_mut(ghost!((*self.perm).borrow_mut(&self.lock.lft_tok))) }
    }

    #[requires(tokens.contains(SPIN_LOCK()))]
    #[requires(self.inv.get(self@))]
    pub fn unlock(self, tokens: Ghost<Tokens>) {
        self.lock.atomic.store(
            false,
            ghost!(|c: &mut Committer<_, _, Ordering::None, Ordering::Release>| {
                self.lock.inner_inv.open(tokens.into_inner(), |inner_inv: &mut SpinLockInv<T>| {
                    inner_inv.excl.valid_op_lemma(&self.excl);
                    inner_inv.excl = self.excl.into_inner();
                    let (mut view, perm) = AtView::new(self.perm).into_inner();
                    c.shoot_store(&mut inner_inv.perm_atomic, &mut view);
                    inner_inv.perm = Some(perm);
                    inner_inv.ts = Some(*snapshot!(c.timestamp() + 1).into_ghost());
                })
            }),
        );
    }
}
