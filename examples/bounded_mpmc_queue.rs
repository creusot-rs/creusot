//! This implementation is an adaption from:
//! https://sites.google.com/site/1024cores/home/lock-free-algorithms/queues/bounded-mpmc-queue

#![allow(unused)]

// use core::marker::PhantomData;

use core::cmp::Ordering;
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
    items_own: Seq<Perm<PermCell<Option<T>>>>,
    statuses_own: Seq<Perm<AtomicUsize>>,

    state_auth: Authority<Option<Excl<(SyncView, SyncView, Seq<(usize, SyncView)>)>>>,
    statuses_auth: Authority<FMap<Int, StatusWithView>>,
    tokens_auth: fmap_view::Authority<Int, Excl<Sum<(), (usize, SyncView)>>>,
    // tokens_frag: fmap_view::Fragment<Int, Excl<Sum<(), (usize, SyncView)>>>,
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
            let C = self.statuses_own.len();
            forall<t_head, t_tail, t_statuses: Seq<_>>
            exists<h, H, t, T, values: Seq<_>, statuses: Seq<_>>
                // 0 <= t <= h <= t + C
                (0 <= t && t <= h && h <= t + C) &&

                // tail ~> (t, T) * head ~> (h, H)
                (match (self.head_own.val().get(t_head), self.tail_own.val().get(t_tail)) {
                    (Some((h2, H2)), Some((t2, T2))) => h == h2@ && t == t2@ && H == H2 && T == T2,
                    _ => true
                }) &&

                // statuses ~>* [(s_0, S_0), ..., (s_C - 1, S_C - 1)]
                (forall<i> 0 <= i && i < C ==>
                     match (self.statuses_own[i].val().get(t_statuses[i])) {
                         Some(s) => statuses[i] == s,
                         _ => true
                     }) &&

                // •(T, H, [(v_t, V_t), ..., (v_h - 1, V_h - 1)])
                (self.state_auth@ == Some(Excl((H, T, values)))) &&

                // { i -> •(s_i, S_i) | 0 <= i < C }
                // TODO

                // •({ k -> ()         | h - C <= k < t }
                //   { k -> (v_k, V_k) |     t <= k < h })
                (forall<k>
                    (h - C <= k && k < t ==> self.tokens_auth@.get(k) == Some(Excl(Sum::Left(())))) &&
                    (t <= k && k < h ==> self.tokens_auth@.get(k) == Some(Excl(Sum::Right(values[k])))))

                // TODO: Available
                // TODO: Occupied
        }
    }
}

struct StatusWithView {
    pub status: Int,
    pub view: SyncView,
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

struct Queue<T, const N: usize> {
    items: [QueueCell<T>; N],
    head: AtomicUsize,
    tail: AtomicUsize,
    inv: Ghost<AtomicInvariant<QueueInv<T>>>,
}

struct QueueCell<T> {
    item: PermCell<Option<T>>,
    status: AtomicUsize,
}

impl<T> QueueCell<T> {
    // TODO: [VL] const
    fn new(
        init: usize,
    ) -> (QueueCell<T>, Ghost<Perm<AtomicUsize>>, Ghost<Perm<PermCell<Option<T>>>>) {
        let (status, at_own) = AtomicUsize::new(init, SyncView::new().borrow_mut());

        let (v, own) = PermCell::new(None);
        (QueueCell { item: v, status }, at_own, own)
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
            }),
            snapshot!(BOUNDED_MPMC_QUEUE()),
        );

        Queue { items, head, tail, inv }
    }

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

        *unsafe { cell.item.borrow_mut(Ghost::conjure()) } = Some(item);
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

        let item = unsafe { cell.item.borrow_mut(Ghost::conjure()) }.take();
        cell.status.store(tail + N, ghost! { |c: &mut Committer<_, _, _, Release>| {} });

        item
    }
}
