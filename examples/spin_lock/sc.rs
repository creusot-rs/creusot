use core::sync::atomic::Ordering;

use creusot_std::{
    cell::PCell,
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

type UpdateCommitter = Committer<AtomicBool, bool, SeqCst, SeqCst>;
type StoreCommitter = Committer<AtomicBool, bool, (), SeqCst>;

struct SpinLockInv<T> {
    cell: Snapshot<PCell<T>>,
    lft: Snapshot<Lifetime>,
    data_perm: Option<Guarded<FullBorrow<Perm<PCell<T>>>, PCell<T>>>,
    flag_perm: Perm<AtomicBool>,
    inv: Snapshot<Mapping<T, bool>>,
}

impl<T> Protocol for SpinLockInv<T> {
    type Public = (PCell<T>, AtomicBool, Lifetime, Mapping<T, bool>);

    #[logic]
    fn public(self) -> Self::Public {
        (*self.cell, *self.flag_perm.ward(), *self.lft, *self.inv)
    }

    #[logic]
    fn protocol(self) -> bool {
        pearlite! {
            let (cell, _, lft, inv) = self.public();

            match (self.flag_perm.val(), self.data_perm) {
                (true, None) => true,
                (false, Some(bor)) => {
                    bor.inner.lft() == lft &&
                    bor.guard() == cell &&
                    inv.get(bor.inner.cur().val())
                },
                _ => false,
            }
        }
    }
}

pub struct SpinLock<T> {
    flag: AtomicBool,
    data: PCell<T>,
    lft_tok: Ghost<LifetimeToken>,
    end: Ghost<EndBorrow<Perm<PCell<T>>>>,
    inner_inv: Ghost<AtomicInvariantSC<SpinLockInv<T>>>,
    pub inv: Snapshot<Mapping<T, bool>>,
}

impl<T> Invariant for SpinLock<T> {
    #[logic(prophetic)]
    fn invariant(self) -> bool {
        pearlite! {
            self.inner_inv.public() == (self.data, self.flag, self.lft_tok.lft(), *self.inv)
                && self.lft_tok.frac() == PositiveReal::from_int(1)
                && self.end.lft() == self.lft_tok.lft()
                && *(^self.end).ward() == self.data
                && self.inner_inv.namespace() == SPIN_LOCK()
        }
    }
}

pub struct SpinLockGuard<'a, T> {
    lock: &'a SpinLock<T>,
    data_perm: Ghost<Guarded<FullBorrow<Perm<PCell<T>>>, PCell<T>>>,
    pub inv: Snapshot<Mapping<T, bool>>,
}

impl<'a, T> View for SpinLockGuard<'a, T> {
    type ViewTy = T;

    #[logic]
    fn view(self) -> T {
        self.data_perm.inner.cur().val()
    }
}

impl<'a, T> Invariant for SpinLockGuard<'a, T> {
    #[logic]
    fn invariant(self) -> bool {
        self.data_perm.guard() == self.lock.data
            && self.data_perm.inner.lft() == self.lock.lft_tok.lft()
            && self.inv == self.lock.inv
    }
}

impl<T> SpinLock<T> {
    #[requires(inv.get(data))]
    #[ensures(result.inv == inv)]
    pub fn new(data: T, inv: Snapshot<Mapping<T, bool>>) -> Self {
        let (data, data_perm) = PCell::new(data);

        let lft_tok = ghost!(LifetimeToken::new());
        let (bor, end) = ghost!(FullBorrow::new(data_perm, snapshot!(lft_tok.lft()))).split();
        let bor = ghost!(bor.into_inner().into_inner());
        let end = ghost!(end.into_inner().into_inner());

        let (flag, flag_perm) = AtomicBool::new(false);

        let inner_inv = ghost!(
            AtomicInvariantSC::new(
                ghost!(SpinLockInv {
                    cell: snapshot!(data),
                    lft: snapshot!(lft_tok.lft()),
                    data_perm: Some(bor.into_inner().add_guard(snapshot!(data))),
                    flag_perm: flag_perm.into_inner(),
                    inv
                }),
                snapshot!(SPIN_LOCK()),
            )
            .into_inner()
        );

        SpinLock { flag, data, lft_tok, end, inner_inv, inv }
    }

    #[requires(tokens.contains(SPIN_LOCK()))]
    #[ensures(self.inv.get(result@))]
    #[ensures(result.inv == self.inv)]
    pub fn lock<'a, 'b>(&'a self, mut tokens: Ghost<Tokens<'b>>) -> SpinLockGuard<'a, T> {
        let mut data_perm = ghost!(None);

        #[invariant(tokens.contains(SPIN_LOCK()))]
        while let Err(_) = self.flag.compare_exchange_weak(
            false,
            true,
            Ordering::SeqCst,
            Ordering::SeqCst,
            ghost! { |c: Result<&mut UpdateCommitter, &_>| {
                if let Ok(c) = c {
                    self.inner_inv.open(tokens.reborrow(), |inner_inv: &mut SpinLockInv<T>| {
                        c.shoot_load(&inner_inv.flag_perm);
                        c.shoot_store(&mut inner_inv.flag_perm);
                        *data_perm = inner_inv.data_perm.take();
                    })
                }
            }},
        ) {}

        SpinLockGuard {
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

impl<'a, T> SpinLockGuard<'a, T> {
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

    #[requires(tokens.contains(SPIN_LOCK()))]
    #[requires(self.inv.get(self@))]
    pub fn unlock(self, tokens: Ghost<Tokens>) {
        self.lock.flag.store(
            false,
            Ordering::SeqCst,
            ghost! { |c: &mut StoreCommitter| {
                self.lock.inner_inv.open(tokens.into_inner(), |inner_inv: &mut SpinLockInv<T>| {
                    c.shoot_store(&mut inner_inv.flag_perm);
                    inner_inv.data_perm = Some(self.data_perm.into_inner());
                })
            }},
        );
    }
}
