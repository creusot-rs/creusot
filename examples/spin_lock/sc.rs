use creusot_std::{
    cell::PermCell,
    ghost::{
        invariant::{AtomicInvariantSC, Protocol, Tokens, declare_namespace},
        lifetime_logic::{EndBorrow, FullBorrow, Lifetime, LifetimeToken},
        perm::Perm,
    },
    invariant::Guarded,
    logic::{Mapping, real::PositiveReal},
    prelude::*,
    std::sync::{
        atomic_sc::{AtomicBool, ordering::SeqCst},
        committer::Committer,
    },
};

declare_namespace! { SPIN_LOCK }

struct SpinLockInv<T> {
    cell: Snapshot<PermCell<T>>,
    lft: Snapshot<Lifetime>,
    perm: Option<Guarded<FullBorrow<Perm<PermCell<T>>>>>,
    perm_atomic: Perm<AtomicBool>,
    inv: Snapshot<Mapping<T, bool>>,
}

impl<T> Protocol for SpinLockInv<T> {
    type Public = (PermCell<T>, AtomicBool, Lifetime, Mapping<T, bool>);

    #[logic]
    fn public(self) -> Self::Public {
        (*self.cell, *self.perm_atomic.ward(), *self.lft, *self.inv)
    }

    #[logic]
    fn protocol(self) -> bool {
        match (self.perm_atomic.val(), self.perm) {
            (true, None) => true,
            (false, Some(bor)) => {
                bor.inner.lft() == *self.lft
                    && bor.guard() == (|b: FullBorrow<Perm<_>>| *b.cur().ward() == *self.cell)
                    && self.inv.get(bor.inner.cur().val())
            }
            _ => false,
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
    #[logic(prophetic)]
    fn invariant(self) -> bool {
        pearlite! {
            self.inner_inv.public() == (self.data, self.atomic, self.lft_tok.lft(), *self.inv)
                && self.lft_tok.frac() == PositiveReal::from_int(1)
                && self.end.lft() == self.lft_tok.lft()
                && *(^self.end).ward() == self.data
                && self.inner_inv.namespace() == SPIN_LOCK()
        }
    }
}

pub struct SpinLockGuard<'a, T> {
    lock: &'a SpinLock<T>,
    perm: Ghost<Guarded<FullBorrow<Perm<PermCell<T>>>>>,
    pub inv: Snapshot<Mapping<T, bool>>,
}

impl<'a, T> View for SpinLockGuard<'a, T> {
    type ViewTy = T;

    #[logic]
    fn view(self) -> T {
        self.perm.inner.cur().val()
    }
}

impl<'a, T> Invariant for SpinLockGuard<'a, T> {
    #[logic]
    fn invariant(self) -> bool {
        self.perm.guard() == (|b: FullBorrow<Perm<_>>| *b.cur().ward() == self.lock.data)
            && self.perm.inner.lft() == self.lock.lft_tok.lft()
            && self.inv == self.lock.inv
    }
}

impl<T> SpinLock<T> {
    #[requires(inv.get(data))]
    #[ensures(result.inv == inv)]
    pub fn new(data: T, inv: Snapshot<Mapping<T, bool>>) -> Self {
        let (atomic, perm_atomic) = AtomicBool::new(false);
        let (data, perm_data) = PermCell::new(data);
        let lft_tok = ghost!(LifetimeToken::new());
        let (bor, end) = FullBorrow::new(perm_data, snapshot!(lft_tok.lft()));
        let inner_inv = AtomicInvariantSC::new(
            ghost!(SpinLockInv {
                cell: snapshot!(data),
                lft: snapshot!(lft_tok.lft()),
                perm: Some(bor.into_inner().add_guard(snapshot!(|p: Perm<_>| *p.ward() == data))),
                perm_atomic: perm_atomic.into_inner(),
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

        #[invariant(tokens.contains(SPIN_LOCK()))]
        while let Err(_) = self.atomic.compare_exchange_weak(
            false,
            true,
            ghost!(|c: Result<&mut Committer<_, _, SeqCst, SeqCst>, &_>| {
                if let Ok(c) = c {
                    self.inner_inv.open(tokens.reborrow(), |inv: &mut SpinLockInv<T>| {
                        c.shoot_load(&inv.perm_atomic);
                        c.shoot_store(&mut inv.perm_atomic);
                        *perm = inv.perm.take();
                    })
                }
            }),
        ) {}

        SpinLockGuard { lock: self, perm: ghost!(perm.into_inner().unwrap()), inv: self.inv }
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
        unsafe { self.lock.data.borrow(ghost!(self.perm.inner.borrow(&self.lock.lft_tok))) }
    }

    #[ensures(*result == self@ && ^result == (^self)@)]
    #[ensures((*self).inv == (^self).inv)]
    pub fn deref_mut(&mut self) -> &mut T {
        ghost_let!(p = &mut self.perm.inner);
        unsafe { self.lock.data.borrow_mut(ghost!(p.into_inner().borrow_mut(&self.lock.lft_tok))) }
    }

    #[requires(tokens.contains(SPIN_LOCK()))]
    #[requires(self.inv.get(self@))]
    pub fn unlock(self, tokens: Ghost<Tokens>) {
        self.lock.atomic.store(
            false,
            ghost!(|c: &mut Committer<_, _, _, SeqCst>| {
                self.lock.inner_inv.open(tokens.into_inner(), |inv: &mut SpinLockInv<T>| {
                    c.shoot_store(&mut inv.perm_atomic);
                    inv.perm = Some(self.perm.into_inner());
                })
            }),
        );
    }
}
