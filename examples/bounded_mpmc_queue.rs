//! This implementation is an adaption from:
//! https://sites.google.com/site/1024cores/home/lock-free-algorithms/queues/bounded-mpmc-queue

#![allow(unused)]

use core::{cmp::Ordering, mem::MaybeUninit};
use creusot_std::{
    cell::PermCell,
    ghost::{
        invariant::{AtomicInvariant, Protocol, declare_namespace},
        perm::Perm,
        resource::{Authority, Fragment, fmap_view},
    },
    logic::{
        FMap, Id,
        ra::{excl::Excl, lattice::SemiLattice, sum::Sum},
        seq::Seq,
    },
    ord_laws_impl,
    prelude::*,
    std::sync::{
        atomic::{
            AtomicUsize,
            ordering::{Acquire, Relaxed, Release},
        },
        committer::Committer,
        view::SyncView,
    },
};

declare_namespace! { BOUNDED_MPMC_QUEUE }

struct QueueInv<T> {
    head_own: Perm<AtomicUsize>,
    tail_own: Perm<AtomicUsize>,
    items_own: Seq<Perm<PermCell<MaybeUninit<T>>>>, // = N [0; N]
    statuses_own: Seq<Perm<AtomicUsize>>,

    state_auth: Authority<Option<Excl<Seq<(usize, SyncView)>>>>,
    statuses_auth: Authority<FMap<Int, StatusWithView>>,
    tokens_auth: fmap_view::Authority<Int, Excl<Option<(usize, SyncView)>>>,

    head: Snapshot<Int>,
    tail: Snapshot<Int>,
    values: Snapshot<Seq<(usize, SyncView)>>, // = self.head - self.tail
    items: Snapshot<Seq<Option<(Perm<PermCell<MaybeUninit<T>>>)>>>, // Fragment<...>
}

impl<T> Protocol for QueueInv<T> {
    type Public = (AtomicUsize, AtomicUsize /*, Seq?, Seq? */, Id, Id, Id);

    #[logic]
    fn public(self) -> Self::Public {
        (
            *self.head_own.ward(),
            *self.tail_own.ward(),
            /*, ..., ... */
            self.state_auth.id(),
            self.statuses_auth.id(),
            self.tokens_auth.id(),
        )
    }

    #[logic(inline)]
    fn protocol(self) -> bool {
        pearlite! {
            let len = self.statuses_own.len();

            // 0 <= t <= h <= t + len
            (0 <= *self.tail && *self.tail <= *self.head && *self.head <= *self.tail + len) &&

            // head ~> (h, H)
            (forall<ts>
                self.head_own.val().contains(ts) ==>
                    self.head_own.val()[ts].0@ == *self.head ||
                    self.head_own.val().contains(ts + 1)
            ) &&

            // tail ~> (t, T)
            (forall<ts>
                self.tail_own.val().contains(ts) ==>
                    self.tail_own.val()[ts].0@ == *self.tail ||
                    self.tail_own.val().contains(ts + 1)
            ) &&

            // statuses ~>* [(s_0, S_0), ..., (s_len - 1, S_len - 1)]
            (forall<i> 0 <= i && i < len ==> self.statuses_auth@.get(i) != None &&
             forall<ts>
                 match (self.statuses_own[i].val().get(ts)) {
                     Some((status, view)) => StatusWithView { status, view } <= self.statuses_auth@[i],
                     _ => true
                 }) &&

            self.state_auth@ == Some(Excl(*self.values)) &&
            self.values.len() == *self.head - *self.tail &&

            // •({ k -> ()         | h - len <= k < t }
            //   { k -> (v_k, V_k) |       t <= k < h })
            (forall<k> *self.head - len <= k && k < *self.tail ==> self.tokens_auth@.get(k) == Some(Excl(None))) &&
            (forall<k> *self.tail <= k && k < *self.head ==> self.tokens_auth@.get(k) == Some(Excl(Some(self.values[k - *self.tail]))))

            // TODO: Available
            // TODO: Occupied
        }
    }
}

struct StatusWithView {
    pub status: usize,
    pub view: SyncView,
}

impl OrdLogic for StatusWithView {
    #[logic(open)]
    fn cmp_log(self, other: Self) -> Ordering {
        if self.status.cmp_log(other.status) == Ordering::Equal {
            other.view.cmp_log(self.view)
        } else {
            self.status.cmp_log(other.status)
        }
    }

    ord_laws_impl! {}
}

impl SemiLattice for StatusWithView {
    #[logic]
    #[ensures(self <= result)]
    #[ensures(other <= result)]
    #[ensures(forall<r> self <= r ==> other <= r ==> result <= r)]
    fn join(self, other: Self) -> Self {
        match self.status.cmp_log(other.status) {
            Ordering::Less => other,
            Ordering::Greater => self,
            Ordering::Equal => {
                StatusWithView { status: self.status, view: self.view.meet(other.view) }
            }
        }
    }
}

struct Queue<T, const N: usize> {
    items: [QueueCell<T>; N],
    head: AtomicUsize,
    tail: AtomicUsize,
    inv: Ghost<AtomicInvariant<QueueInv<T>>>,
}

// TODO: [VL] Invariant on Queue that links public part of the invariant to items/head/tail/N
struct QueueCell<T> {
    item: PermCell<MaybeUninit<T>>,
    status: AtomicUsize,
}

impl<T> QueueCell<T> {
    fn new(
        init: usize,
    ) -> (QueueCell<T>, Ghost<Perm<AtomicUsize>>, Ghost<Perm<PermCell<MaybeUninit<T>>>>) {
        let (status, at_own) = AtomicUsize::new(init, SyncView::new().borrow_mut());

        let (item, own) = PermCell::new(MaybeUninit::uninit());
        (QueueCell { item, status }, at_own, own)
    }
}

impl<T, const N: usize> Queue<T, N> {
    pub fn new() -> Queue<T, N> {
        let mut items_own = Seq::new();
        let mut statuses_own = Seq::new();

        let items = core::array::from_fn(|i| {
            let (item, at_own, own) = QueueCell::new(i);
            ghost! {
                items_own.push_back_ghost(own.into_inner());
                statuses_own.push_back_ghost(at_own.into_inner());
            };
            item
        });

        let (head, head_own) = AtomicUsize::new(0, SyncView::new().borrow_mut());
        let (tail, tail_own) = AtomicUsize::new(0, SyncView::new().borrow_mut());

        let inv = AtomicInvariant::new(
            ghost!(QueueInv {
                head_own: head_own.into_inner(),
                tail_own: tail_own.into_inner(),
                items_own: items_own.into_inner(),
                statuses_own: statuses_own.into_inner(),

                state_auth: Authority::alloc().into_inner(),
                statuses_auth: Authority::alloc().into_inner(),
                tokens_auth: fmap_view::Authority::new().into_inner(),

                head: snapshot!(1),
                tail: snapshot!(0),
                values: snapshot!(Seq::empty()),
                items: snapshot!(Seq::empty())
            }),
            snapshot!(BOUNDED_MPMC_QUEUE()),
        );

        Queue { items, head, tail, inv }
    }

    // TODO [VL]: Add a user committer at the serialisation point
    // It might only contains •([(v_t, V_t), ..., [(v_h-1, V_h-1)]])
    pub fn try_enqueue(&self, item: T) -> bool {
        let head = self.head.load(ghost! { |c: &Committer<_, _, Relaxed, _>| {} });

        let cell = &self.items[head % N];
        let status = cell.status.load(ghost! { |c: &Committer<_, _, Acquire, _>| {} });

        if head != status {
            return false;
        }

        let res = self.head.compare_exchange_weak::<_, Relaxed, Relaxed>(
            head,
            head + 1,
            ghost! { |c: Result<&mut _, &_>| {}},
        );

        if res.is_err() {
            return false;
        }

        unsafe { cell.item.set(Ghost::conjure(), MaybeUninit::new(item)) };
        cell.status.store(head + 1, ghost! { |c: &mut Committer<_, _, _, Release>| {} });

        true
    }

    pub fn try_dequeue(&self) -> Option<T> {
        let tail = self.tail.load(ghost! { |c: &Committer<_, _, Relaxed, _>| {} });

        let cell = &self.items[tail % N];
        let status = cell.status.load(ghost! { |c: &Committer<_, _, Acquire, _>| {} });

        if tail + 1 != status {
            return None;
        }

        let res = self.tail.compare_exchange_weak::<_, Relaxed, Relaxed>(
            tail,
            tail + 1,
            ghost! { |c: Result<&mut _, &_>| {}},
        );

        if res.is_err() {
            return None;
        }

        let item = unsafe {
            let v = cell.item.replace(Ghost::conjure(), MaybeUninit::uninit());
            v.assume_init()
        };
        cell.status.store(tail + N, ghost! { |c: &mut Committer<_, _, _, Release>| {} });

        Some(item)
    }
}
