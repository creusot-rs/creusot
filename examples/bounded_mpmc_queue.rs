//! This implementation is an adaption from:
//! https://sites.google.com/site/1024cores/home/lock-free-algorithms/queues/bounded-mpmc-queue

// use core::marker::PhantomData;

use creusot_std::{
    cell::PermCell,
    ghost::{
        invariant::{AtomicInvariant, Protocol, declare_namespace},
        perm::Perm,
        resource::Authority,
    },
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
}

impl<T> Protocol for QueueInv<T> {
    type Public = (AtomicUsize, AtomicUsize);

    #[logic]
    fn public(self) -> Self::Public {
        (*self.head_own.ward(), *self.tail_own.ward())
    }

    #[logic(inline)]
    fn protocol(self) -> bool {
        true
    }
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
