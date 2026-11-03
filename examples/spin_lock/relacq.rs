use core::sync::atomic::Ordering;

use creusot_std::{
    cell::PCell,
    ghost::{
        invariant::{AtomicInvariant, Protocol, Tokens, declare_namespace},
        lifetime_logic::{EndBorrow, FullBorrow, Lifetime, LifetimeToken},
        perm::Perm,
        resource::Resource,
    },
    invariant::Guarded,
    logic::{Id, Mapping, ra::excl::Excl, real::PositiveReal},
    prelude::*,
    std::sync::{
        atomic::{
            AtomicBool,
            ordering::{Acquire, Relaxed, Release},
        },
        committer::Committer,
        view::{AtView, HasTimestamp, ReleaseSyncView, SyncView, Timestamp},
    },
};

declare_namespace! { SPIN_LOCK }

type UpdateCommitter = Committer<AtomicBool, bool, Acquire, Relaxed>;
type StoreCommitter = Committer<AtomicBool, bool, (), Release>;

struct SpinLockInv<T> {
    cell: Snapshot<PCell<T>>,
    lft: Snapshot<Lifetime>,
    data_perm: Option<AtView<Guarded<FullBorrow<Perm<PCell<T>>>, PCell<T>>>>,
    flag_perm: Perm<AtomicBool>,
    excl: Resource<Option<Excl<()>>>,
    ts: Option<Timestamp>,
    inv: Snapshot<Mapping<T, bool>>,
}

impl<T> Protocol for SpinLockInv<T> {
    type Public = ((PCell<T>, AtomicBool, Lifetime, Mapping<T, bool>), Id);

    #[logic]
    fn public(self) -> Self::Public {
        ((*self.cell, *self.flag_perm.ward(), *self.lft, *self.inv), self.excl.id())
    }

    #[logic]
    fn protocol(self) -> bool {
        pearlite! {
            let ((cell, _, lft, inv), _) = self.public();

            (forall<t, view> self.flag_perm.val().lookup(t) == Some((false, view)) ==>
                Some(t) == self.ts || self.flag_perm.val().lookup(t + 1) != None) &&
            match (self.data_perm, self.ts, self.excl.val()) {
                (None, None, None) => true,
                (Some(bor), Some(ts), Some(_)) => {
                    bor.view() <= self.flag_perm.val()[ts].1 &&
                    bor.val().inner.lft() == lft &&
                    bor.val().guard() == cell &&
                    inv.get(bor.val().inner.cur().val())
                },
                _ => false
            }
        }
    }
}

pub struct SpinLock<T> {
    flag: AtomicBool,
    data: PCell<T>,
    lft_tok: Ghost<LifetimeToken>,
    end: Ghost<EndBorrow<Perm<PCell<T>>>>,
    inner_inv: Ghost<AtomicInvariant<SpinLockInv<T>>>,
    pub inv: Snapshot<Mapping<T, bool>>,
}

impl<T> Invariant for SpinLock<T> {
    #[logic(prophetic)]
    fn invariant(self) -> bool {
        pearlite! {
            let (public, _) = self.inner_inv.public();

            public == (self.data, self.flag, self.lft_tok.lft(), *self.inv)
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
    excl: Ghost<Resource<Option<Excl<()>>>>,
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
        let (_, id) = self.lock.inner_inv.public();

        self.data_perm.guard() == self.lock.data
            && self.data_perm.inner.lft() == self.lock.lft_tok.lft()
            && self.excl.val() != None
            && self.excl.id() == id
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
        let bor = ghost!(bor.into_inner().into_inner().add_guard(snapshot!(data)));
        let end = ghost!(end.into_inner().into_inner());

        let (mut view, data_perm) = ghost!(AtView::new(bor).into_inner()).split();
        let (flag, flag_perm) = AtomicBool::new(false, ghost!(&mut *view));

        let inner_inv = ghost!(
            AtomicInvariant::new(
                ghost!(SpinLockInv {
                    cell: snapshot!(data),
                    lft: snapshot!(lft_tok.lft()),
                    data_perm: Some(data_perm.into_inner()),
                    flag_perm: flag_perm.into_inner(),
                    excl: Resource::alloc(snapshot!(Some(Excl(())))).into_inner(),
                    ts: Some(*snapshot!(flag.get_timestamp(*view)).into_ghost()),
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
        let mut excl = ghost!(None);

        #[invariant(tokens.contains(SPIN_LOCK()))]
        while let Err(_) = self.flag.compare_exchange_weak::<_, Acquire, Relaxed>(
            false,
            true,
            Ordering::Acquire,
            Ordering::Relaxed,
            ghost! { |c: Result<&mut UpdateCommitter, &_>| {
                if let Ok(c) = c {
                    self.inner_inv.open(tokens.reborrow(), |inner_inv: &mut SpinLockInv<T>| {
                        let mut view = *SyncView::new();
                        c.shoot_load(&inner_inv.flag_perm, &mut view);
                        c.shoot_store(
                            &mut inner_inv.flag_perm,
                            &mut view,
                            *ReleaseSyncView::new(),
                        );
                        proof_assert!(Some(c.timestamp()) == inner_inv.ts);
                        *data_perm = Some(inner_inv.data_perm.take().unwrap().sync(view));
                        *excl = Some(
                            inner_inv.excl.split_off(snapshot!(Some(Excl(()))), snapshot!(None)),
                        );
                        inner_inv.ts = None
                    })
                }
            }},
        ) {}

        SpinLockGuard {
            lock: self,
            data_perm: ghost!(data_perm.into_inner().unwrap()),
            excl: ghost!(excl.into_inner().unwrap()),
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
            Ordering::Release,
            ghost! { |c: &mut StoreCommitter| {
                self.lock.inner_inv.open(tokens.into_inner(), |inner_inv: &mut SpinLockInv<T>| {
                    inner_inv.excl.valid_op_lemma(&self.excl);
                    inner_inv.excl = self.excl.into_inner();
                    let (mut view, data_perm) = AtView::new(self.data_perm).into_inner();
                    c.shoot_store(&mut inner_inv.flag_perm, &mut view);
                    inner_inv.data_perm = Some(data_perm);
                    inner_inv.ts = Some(*snapshot!(c.timestamp() + 1).into_ghost());
                })
            }},
        );
    }
}
