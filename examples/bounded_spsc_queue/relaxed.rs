// DEPTH 10

// Single-producer single-consumer bounded queue, in the relaxed memory model.
//
// Translated from the Verus version:
// <https://github.com/zero-to-nat/verus-relaxed-memory/blob/pldi2027-cleanup/wm-examples/src/spsc.rs>

use core::{
    mem::{MaybeUninit, replace},
    sync::atomic::Ordering,
};

use creusot_std::{
    cell::PCell,
    ghost::{
        FnGhost,
        invariant::{AtomicInvariant, Protocol, Tokens, declare_namespace},
        perm::Perm,
    },
    logic::{FMap, Id, Mapping},
    prelude::*,
    std::sync::{
        atomic::{
            AtomicUsize,
            ordering::{Acquire, Release},
        },
        committer::Committer,
        view::{AtView, SyncView, Timestamp},
    },
};

#[cfg(creusot)]
use creusot_std::std::sync::view::HasTimestamp;

declare_namespace! { BOUNDED_SPSC_QUEUE }

/// A ghost variable, split in two halves: an authority (held by the invariant) and a
/// fragment (held by a client). Both halves agree on the value, and updating the
/// value requires both halves. This corresponds to `FracGhost` with fraction 1/2 in Verus.
mod ghost_var {
    use creusot_std::{
        ghost::resource,
        logic::{Id, ra::excl::Excl},
        prelude::*,
    };

    pub struct Authority<T>(resource::Authority<Option<Excl<T>>>);
    pub struct Fragment<T>(resource::Fragment<Option<Excl<T>>>);

    impl<T> Invariant for Authority<T> {
        #[logic(inline)]
        fn invariant(self) -> bool {
            self.0.view() != None
        }
    }

    impl<T> Invariant for Fragment<T> {
        #[logic(inline)]
        fn invariant(self) -> bool {
            self.0.view() != None
        }
    }

    impl<T> Authority<T> {
        #[logic]
        pub fn id(self) -> Id {
            self.0.id()
        }

        #[logic]
        pub fn val(self) -> T {
            self.0.view().unwrap_logic().0
        }

        #[check(ghost)]
        #[ensures(result.0.id() == result.1.id())]
        #[ensures(result.0.val() == *v && result.1.val() == *v)]
        pub fn alloc(v: Snapshot<T>) -> Ghost<(Authority<T>, Fragment<T>)> {
            ghost! {
                let mut auth = resource::Authority::alloc().into_inner();
                let frag = auth.add_fragment(snapshot!(Some(Excl(*v))));
                (Authority(auth), Fragment(frag))
            }
        }

        #[check(ghost)]
        #[requires(self.id() == frag.id())]
        #[ensures(self.val() == frag.val())]
        pub fn agree(&self, frag: &Fragment<T>) {
            self.0.frag_lemma(&frag.0);
        }

        #[check(ghost)]
        #[requires((*self).id() == (*frag).id())]
        #[ensures((^self).id() == (*self).id())]
        #[ensures((^frag).id() == (*frag).id())]
        #[ensures((*self).val() == (*frag).val())]
        #[ensures((^self).val() == *v && (^frag).val() == *v)]
        pub fn update(&mut self, frag: &mut Fragment<T>, v: Snapshot<T>) {
            let upd = snapshot!(Some(Excl(*v)));
            self.0.update(&mut frag.0, snapshot!((*upd, *upd)));
        }
    }

    impl<T> Fragment<T> {
        #[logic]
        pub fn id(self) -> Id {
            self.0.id()
        }

        #[logic]
        pub fn val(self) -> T {
            self.0.view().unwrap_logic().0
        }
    }
}

use ghost_var::{Authority, Fragment};

pub struct ProducerState {
    pub head: Int,
    pub view: SyncView,
    pub producing: bool,
}

pub struct ConsumerState {
    pub tail: Int,
    pub view: SyncView,
    pub consuming: bool,
}

type PermPCell<T> = Perm<PCell<MaybeUninit<T>>>;

pub struct QueueContents<T>(Fragment<Seq<T>>);

impl<T> QueueContents<T> {
    #[logic]
    pub fn id(self) -> Id {
        self.0.id()
    }
}

impl<T> View for QueueContents<T> {
    type ViewTy = Seq<T>;

    #[logic]
    fn view(self) -> Seq<T> {
        self.0.val()
    }
}

struct QueueInv<T> {
    head_own: Perm<AtomicUsize>,
    tail_own: Perm<AtomicUsize>,

    cells: Snapshot<Seq<PCell<MaybeUninit<T>>>>,
    cell_perms: FMap<Int, AtView<PermPCell<T>>>,

    producer_auth: Authority<ProducerState>,
    consumer_auth: Authority<ConsumerState>,
    contents_auth: Authority<Seq<T>>,

    head_logical: Snapshot<Mapping<Timestamp, Int>>,
    tail_logical: Snapshot<Mapping<Timestamp, Int>>,
}

impl<T> QueueInv<T> {
    #[logic]
    fn len(self) -> Int {
        self.cells.len()
    }

    #[logic]
    fn mod_len(self, i: Int) -> Int {
        i.rem_euclid(self.len())
    }

    #[logic]
    fn producer(self) -> ProducerState {
        self.producer_auth.val()
    }

    #[logic]
    fn consumer(self) -> ConsumerState {
        self.consumer_auth.val()
    }

    #[logic]
    fn head(self) -> Int {
        self.producer().head
    }

    #[logic]
    fn tail(self) -> Int {
        self.consumer().tail
    }

    #[logic]
    fn seq(self) -> Seq<T> {
        self.contents_auth.val()
    }

    #[logic]
    fn hl(self, ts: Timestamp) -> Int {
        self.head_logical.get(ts)
    }

    #[logic]
    fn tl(self, ts: Timestamp) -> Int {
        self.tail_logical.get(ts)
    }

    #[logic]
    fn start(self) -> Int {
        if self.consumer().consuming { self.tail() + 1 } else { self.tail() }
    }

    #[logic(inline)]
    fn can_be_consumed(self, i: Int) -> bool {
        self.tail() <= i && i < self.head() && !(self.consumer().consuming && i == self.tail())
    }

    #[logic(inline)]
    fn can_be_produced(self, i: Int) -> bool {
        self.head() <= i
            && i < self.tail() + self.len()
            && !(self.producer().producing && i == self.head())
    }

    #[logic(inline)]
    fn valid_consumable(self, i: Int) -> bool {
        pearlite! {
            match self.cell_perms.lookup(i) {
                Some(p) =>
                    *p.val().ward() == self.cells[self.mod_len(i)] &&
                    p.val().val()@ == Some(self.seq()[i - self.start()]) &&
                    p.view() <= self.producer().view &&
                    // The permission can be acquired from any message of `head` which publishes it.
                    forall<ts> match self.head_own.val().lookup(ts) {
                        Some((_, msg_view)) => self.hl(ts) >= i + 1 ==> p.view() <= msg_view,
                        None => true,
                    },
                None => false,
            }
        }
    }

    #[logic(inline)]
    fn valid_producible(self, i: Int) -> bool {
        pearlite! {
            match self.cell_perms.lookup(i) {
                Some(p) =>
                    *p.val().ward() == self.cells[self.mod_len(i)] &&
                    p.val().val()@ == None &&
                    p.view() <= self.consumer().view &&
                    // The permission can be acquired from any message of `tail` which publishes it.
                    forall<ts> match self.tail_own.val().lookup(ts) {
                        Some((_, msg_view)) => self.tl(ts) >= i - self.len() + 1 ==> p.view() <= msg_view,
                        None => true,
                    },
                None => false,
            }
        }
    }

    /// For any cell that can be consumed/produced, the perm must be present and initialized/uninitialized.
    #[logic(inline)]
    fn valid_storage(self) -> bool {
        pearlite! {
            forall<i> self.tail() <= i && i < self.tail() + self.len() ==>
                (self.can_be_consumed(i) ==> self.valid_consumable(i)) &&
                (self.can_be_produced(i) ==> self.valid_producible(i))
        }
    }

    /// Relation between the messages of the atomics and the logical values.
    #[logic(inline)]
    fn matches_physical_state(self) -> bool {
        pearlite! {
            (forall<ts> match self.head_own.val().lookup(ts) {
                Some((h, _)) =>
                    h@ == self.mod_len(self.hl(ts)) &&
                    self.hl(ts) <= self.head() &&
                    // The producer is the only writer: it has seen all the messages.
                    ts <= self.head_own.ward().get_timestamp(self.producer().view),
                None => true,
            }) &&
            (forall<ts> match self.tail_own.val().lookup(ts) {
                Some((t, _)) =>
                    t@ == self.mod_len(self.tl(ts)) &&
                    self.tl(ts) <= self.tail() &&
                    // The consumer is the only writer: it has seen all the messages.
                    ts <= self.tail_own.ward().get_timestamp(self.consumer().view),
                None => true,
            })
        }
    }

    /// In each history, (logical) values are monotonically increasing by timestamp.
    #[logic(inline)]
    fn history_monotonic(self) -> bool {
        pearlite! {
            (forall<t1, t2> self.head_own.val().contains_logic(t1) && self.head_own.val().contains_logic(t2) && t1 < t2 ==>
                self.hl(t1) < self.hl(t2)) &&
            (forall<t1, t2> self.tail_own.val().contains_logic(t1) && self.tail_own.val().contains_logic(t2) && t1 < t2 ==>
                self.tl(t1) < self.tl(t2))
        }
    }

    /// tail is never ahead of head, and head is never more than (len-1) steps ahead of tail.
    #[logic(inline)]
    fn head_tail_bounds(self) -> bool {
        pearlite! {
            // All the messages of `tail` that the producer may still read have a logical value
            // close enough to the producer's `head`.
            (forall<ts> self.tail_own.val().contains_logic(ts) &&
                self.tail_own.ward().get_timestamp(self.producer().view) <= ts ==>
                self.tl(ts) + self.len() > self.head() &&
                (self.producer().producing ==> self.tl(ts) + self.len() - 1 > self.head())) &&
            // All the messages of `head` that the consumer may still read have a logical value
            // at least the consumer's `tail`.
            (forall<ts> self.head_own.val().contains_logic(ts) &&
                self.head_own.ward().get_timestamp(self.consumer().view) <= ts ==>
                self.hl(ts) >= self.tail() &&
                (self.consumer().consuming ==> self.hl(ts) >= self.tail() + 1)) &&
            self.tail() <= self.head() && self.head() < self.tail() + self.len() &&
            (self.producer().producing ==> self.head() + 1 < self.tail() + self.len()) &&
            (self.consumer().consuming ==> self.tail() < self.head())
        }
    }

    /// The logical contents of the queue are the values of the cells that can be consumed, oldest first.
    #[logic(inline)]
    fn matches_contents(self) -> bool {
        self.seq().len() == self.head() - self.start()
    }

    #[logic]
    #[requires(self.len() > 0)]
    #[ensures(self.mod_len(i + self.len()) == self.mod_len(i))]
    fn mod_len_wrap(self, i: Int) {}
}

impl<T> Protocol for QueueInv<T> {
    type Public = (AtomicUsize, AtomicUsize, Seq<PCell<MaybeUninit<T>>>, Id, Id, Id);

    #[logic]
    fn public(self) -> Self::Public {
        (
            *self.head_own.ward(),
            *self.tail_own.ward(),
            *self.cells,
            self.producer_auth.id(),
            self.consumer_auth.id(),
            self.contents_auth.id(),
        )
    }

    #[logic(inline)]
    fn protocol(self) -> bool {
        self.len() > 0
            && self.head_tail_bounds()
            && self.history_monotonic()
            && self.matches_physical_state()
            && self.valid_storage()
            && self.matches_contents()
    }
}

pub struct Queue<T> {
    buffer: Vec<PCell<MaybeUninit<T>>>,
    head: AtomicUsize,
    tail: AtomicUsize,
    inv: Ghost<AtomicInvariant<QueueInv<T>>>,
}

impl<T> Invariant for Queue<T> {
    #[logic(inline)]
    fn invariant(self) -> bool {
        pearlite! {
            let (head, tail, cells, _, _, _) = self.inv.public();
            head == self.head &&
            tail == self.tail &&
            cells == self.buffer@ &&
            self.buffer@.len() > 0 &&
            self.inv.namespace() == BOUNDED_SPSC_QUEUE()
        }
    }
}

impl<T> Queue<T> {
    #[logic]
    pub fn id(self) -> Id {
        self.inv.public().5
    }

    #[logic]
    fn producer_id(self) -> Id {
        self.inv.public().3
    }

    #[logic]
    fn consumer_id(self) -> Id {
        self.inv.public().4
    }

    #[logic]
    fn mod_len(self, i: Int) -> Int {
        pearlite! { i.rem_euclid(self.buffer@.len()) }
    }
}

pub struct QueueCommitter<'a, T> {
    auth: &'a mut Authority<Seq<T>>,
    id: Snapshot<Id>,
    old_seq: Snapshot<Seq<T>>,
    new_seq: Snapshot<Seq<T>>,
    shot: bool,
}

impl<T> Invariant for QueueCommitter<'_, T> {
    #[logic(inline)]
    fn invariant(self) -> bool {
        self.auth.id() == *self.id
            && if self.shot {
                self.auth.val() == *self.new_seq
            } else {
                self.auth.val() == *self.old_seq
            }
    }
}

impl<T> QueueCommitter<'_, T> {
    #[logic]
    pub fn id(self) -> Id {
        *self.id
    }

    #[logic]
    pub fn old_seq(self) -> Seq<T> {
        *self.old_seq
    }

    #[logic]
    pub fn new_seq(self) -> Seq<T> {
        *self.new_seq
    }

    #[logic]
    pub fn shot(self) -> bool {
        self.shot
    }

    #[requires(!self.shot())]
    #[requires(self.id() == contents.id())]
    #[ensures((^self).shot())]
    #[ensures((*self).hist_inv(^self))]
    #[ensures((*contents)@ == self.old_seq())]
    #[ensures((^contents)@ == self.new_seq())]
    #[ensures((^contents).id() == (*contents).id())]
    #[check(ghost)]
    pub fn shoot(&mut self, contents: &mut QueueContents<T>) {
        self.auth.update(&mut contents.0, self.new_seq);
        self.shot = true;
    }

    #[logic(inline, prophetic)]
    pub fn hist_inv(self, other: Self) -> bool {
        pearlite! {
            self.id == other.id && ^self.auth == ^other.auth &&
            self.old_seq == other.old_seq && self.new_seq == other.new_seq
        }
    }
}

pub struct QueueTokens {
    producer: Fragment<ProducerState>,
    consumer: Fragment<ConsumerState>,
    view: SyncView,
}

impl QueueTokens {
    #[logic]
    pub fn wf<T>(self, queue: Queue<T>) -> bool {
        pearlite! {
            self.producer.id() == queue.producer_id() &&
            self.producer.val() == ProducerState { head: 0, view: self.view, producing: false } &&
            self.consumer.id() == queue.consumer_id() &&
            self.consumer.val() == ConsumerState { tail: 0, view: self.view, consuming: false }
        }
    }
}

impl<T> Queue<T> {
    #[requires(len@ > 0)]
    #[ensures(result.1.wf(result.0))]
    #[ensures(result.2.id() == result.0.id())]
    #[ensures(result.2@ == Seq::empty())]
    pub fn new(len: usize) -> (Self, Ghost<QueueTokens>, Ghost<QueueContents<T>>) {
        let mut buffer: Vec<PCell<MaybeUninit<T>>> = Vec::new();
        let mut cell_perms: Ghost<FMap<Int, AtView<PermPCell<T>>>> =
            ghost!(FMap::new().into_inner());
        let mut view = ghost!(SyncView::new().into_inner());

        #[invariant(buffer@.len() == produced.len())]
        #[invariant(forall<j> 0 <= j && j < produced.len() ==>
            match cell_perms.lookup(j) {
                Some(p) => *p.val().ward() == buffer@[j] && p.val().val()@ == None && p.view() <= *view,
                None => false,
            }
        )]
        for _ in 0..len {
            let (cell, cell_perm) = PCell::new(MaybeUninit::uninit());
            ghost! {
                let (v, at_view) = AtView::new(cell_perm).into_inner();
                view.join_in(v);
                cell_perms.insert(*snapshot!(buffer@.len()).into_ghost(), at_view);
            };
            buffer.push(cell);
        }

        let (head, head_own) = AtomicUsize::new(0, view.borrow_mut());
        let (tail, tail_own) = AtomicUsize::new(0, view.borrow_mut());

        let (producer_auth, producer_frag) = ghost!(
            Authority::alloc(snapshot!(ProducerState { head: 0, view: *view, producing: false }))
                .into_inner()
        )
        .split();

        let (consumer_auth, consumer_frag) = ghost!(
            Authority::alloc(snapshot!(ConsumerState { tail: 0, view: *view, consuming: false }))
                .into_inner()
        )
        .split();

        let (contents_auth, contents_frag) =
            ghost!(Authority::alloc(snapshot!(Seq::empty())).into_inner()).split();

        let inv = ghost!(
            AtomicInvariant::new(
                ghost!(QueueInv {
                    head_own: head_own.into_inner(),
                    tail_own: tail_own.into_inner(),
                    cells: snapshot!(buffer@),
                    cell_perms: cell_perms.into_inner(),
                    producer_auth: producer_auth.into_inner(),
                    consumer_auth: consumer_auth.into_inner(),
                    contents_auth: contents_auth.into_inner(),
                    head_logical: snapshot!(Mapping::cst(0)),
                    tail_logical: snapshot!(Mapping::cst(0)),
                }),
                snapshot!(BOUNDED_SPSC_QUEUE()),
            )
            .into_inner()
        );

        let queue = Queue { buffer, head, tail, inv };
        let tokens = ghost!(QueueTokens {
            producer: producer_frag.into_inner(),
            consumer: consumer_frag.into_inner(),
            view: *view,
        });
        (queue, tokens, ghost!(QueueContents(contents_frag.into_inner())))
    }
}

pub struct Producer<'a, T> {
    queue: &'a Queue<T>,
    head: usize,

    state: Ghost<Fragment<ProducerState>>,
    view: Ghost<SyncView>,
}

impl<T> Invariant for Producer<'_, T> {
    #[logic(inline)]
    fn invariant(self) -> bool {
        pearlite! {
            self.state.id() == self.queue.producer_id() &&
            !self.state.val().producing &&
            self.state.val().view == *self.view &&
            self.head@ == self.queue.mod_len(self.state.val().head)
        }
    }
}

impl<T> Producer<'_, T> {
    #[logic]
    pub fn queue_id(self) -> Id {
        self.queue.id()
    }

    #[requires(tokens.contains(BOUNDED_SPSC_QUEUE()))]
    #[requires(forall<qc: &mut QueueCommitter<T>>
        inv(qc) ==> !qc.shot() ==> qc.id() == self.queue_id() ==> qc.new_seq() == qc.old_seq().snoc(item) ==>
        f.precondition((qc,)) && (f.postcondition_once((qc,), ()) ==> (^qc).shot() && (*qc).hist_inv(^qc))
    )]
    #[ensures(exists<qc: &mut QueueCommitter<T>>
        !qc.shot() && qc.id() == self.queue_id() && qc.new_seq() == qc.old_seq().snoc(item) &&
        f.postcondition_once((qc,), ())
    )]
    #[ensures((^self).queue_id() == (*self).queue_id())]
    pub fn enqueue<F>(&mut self, item: T, mut tokens: Ghost<Tokens>, f: Ghost<F>)
    where
        F: FnGhost + FnOnce(&mut QueueCommitter<T>),
    {
        let queue = self.queue;
        let buffer_size = queue.buffer.len();

        // Calculate the index of the slot right after `head`, wrapping around
        // if necessary. If the enqueue is successful, then we will be updating
        // the `head` to this value.
        let next = if self.head + 1 == buffer_size { 0 } else { self.head + 1 };
        let item_snap = snapshot!(item);

        // Loop: if the queue is full, then block until it is not.
        #[invariant(tokens.contains(BOUNDED_SPSC_QUEUE()))]
        #[invariant(self.queue == queue)]
        #[invariant(next@ == queue.mod_len(self.state.val().head + 1))]
        #[invariant(self.state.id() == queue.producer_id())]
        #[invariant(!self.state.val().producing)]
        #[invariant(self.state.val().view == *self.view)]
        #[invariant(self.head@ == queue.mod_len(self.state.val().head))]
        loop {
            let mut perm: Ghost<Option<PermPCell<T>>> = ghost!(None);

            // Get the current `tail` value from the shared atomic.
            let tail = queue.tail.load(Ordering::Acquire, ghost! { |c: &Committer<_, _, Acquire, _>| {
                queue.inv.open(tokens.reborrow(), |inv: &mut QueueInv<T>| {
                    inv.producer_auth.agree(&self.state);
                    c.shoot_load(&inv.tail_own, &mut self.view);
                    let h = snapshot!(inv.head());
                    snapshot!(inv.mod_len_wrap(*h + 1 - inv.len()));
                    if c.val_load() != next {
                        // update producer state from Idle to Producing
                        let new_state = snapshot!(ProducerState { head: *h, view: *self.view, producing: true });
                        inv.producer_auth.update(&mut self.state, new_state);
                        // remove (uninitialized) permission for head cell
                        let p = inv.cell_perms.delete(&*snapshot!(*h).into_ghost()).unwrap();
                        *perm = Some(p.sync(*self.view));
                    } else {
                        // update producer view in the invariant
                        let new_state = snapshot!(ProducerState { head: *h, view: *self.view, producing: false });
                        inv.producer_auth.update(&mut self.state, new_state);
                    }
                    proof_assert!(inv.valid_storage());
                })
            }});

            if tail != next {
                unsafe {
                    *queue.buffer[self.head].borrow_mut(ghost!(perm.as_mut().unwrap())) =
                        MaybeUninit::new(item)
                };

                queue.head.store(
                    next,
                    Ordering::Release,
                    ghost! { |c: &mut Committer<_, _, _, Release>| {
                        queue.inv.open(tokens.reborrow(), |inv: &mut QueueInv<T>| {
                            inv.producer_auth.agree(&self.state);
                            let h = snapshot!(inv.head());

                            // store subjective cell permission at the thread's new view
                            let (mut new_view, at_view) = AtView::new(ghost!(perm.take().unwrap())).into_inner();
                            new_view.join_in(*self.view);
                            c.shoot_store(&mut inv.head_own, &mut new_view);
                            *self.view = new_view;

                            // update producer state from Producing to Idle
                            let new_state = snapshot!(ProducerState { head: *h + 1, view: *self.view, producing: false });
                            inv.producer_auth.update(&mut self.state, new_state);

                            // linearization point: `item` is added to the end of the queue
                            let old_seq = snapshot!(inv.seq());
                            let new_seq = snapshot!(old_seq.snoc(*item_snap));
                            f.into_inner()(&mut QueueCommitter {
                                auth: &mut inv.contents_auth,
                                id: snapshot!(queue.id()),
                                old_seq,
                                new_seq,
                                shot: false,
                            });

                            // insert (initialized) permission for (old) head cell
                            inv.cell_perms.insert(*snapshot!(*h).into_ghost(), at_view);
                            // update logical value of the new message
                            inv.head_logical = snapshot!(inv.head_logical.set(c.timestamp() + 1, *h + 1));
                        })
                    }},
                );
                self.head = next;
                return;
            }
        }
    }
}

pub struct Consumer<'a, T> {
    queue: &'a Queue<T>,
    tail: usize,

    state: Ghost<Fragment<ConsumerState>>,
    view: Ghost<SyncView>,
}

impl<T> Invariant for Consumer<'_, T> {
    #[logic(inline)]
    fn invariant(self) -> bool {
        pearlite! {
            self.state.id() == self.queue.consumer_id() &&
            !self.state.val().consuming &&
            self.state.val().view == *self.view &&
            self.tail@ == self.queue.mod_len(self.state.val().tail)
        }
    }
}

impl<T> Consumer<'_, T> {
    #[logic]
    pub fn queue_id(self) -> Id {
        self.queue.id()
    }

    #[requires(tokens.contains(BOUNDED_SPSC_QUEUE()))]
    #[requires(forall<qc: &mut QueueCommitter<T>>
        inv(qc) ==> !qc.shot() ==> qc.id() == self.queue_id() ==> qc.old_seq().len() > 0 ==> qc.new_seq() == qc.old_seq().tail() ==>
        f.precondition((qc,)) && (f.postcondition_once((qc,), ()) ==> (^qc).shot() && (*qc).hist_inv(^qc))
    )]
    #[ensures(exists<qc: &mut QueueCommitter<T>>
        !qc.shot() && qc.id() == self.queue_id() &&
        qc.old_seq().len() > 0 && qc.new_seq() == qc.old_seq().tail() &&
        f.postcondition_once((qc,), ()) &&
        result == qc.old_seq()[0]
    )]
    #[ensures((^self).queue_id() == (*self).queue_id())]
    pub fn dequeue<F>(&mut self, mut tokens: Ghost<Tokens>, f: Ghost<F>) -> T
    where
        F: FnGhost + FnOnce(&mut QueueCommitter<T>),
    {
        let queue = self.queue;
        let buffer_size = queue.buffer.len();

        let next = if self.tail + 1 == buffer_size { 0 } else { self.tail + 1 };

        let f_snap = snapshot!(*f);
        let mut f = ghost!(Some(f.into_inner()));

        #[invariant(tokens.contains(BOUNDED_SPSC_QUEUE()))]
        #[invariant(self.queue == queue)]
        #[invariant(next@ == queue.mod_len(self.state.val().tail + 1))]
        #[invariant(self.state.id() == queue.consumer_id())]
        #[invariant(!self.state.val().consuming)]
        #[invariant(self.state.val().view == *self.view)]
        #[invariant(self.tail@ == queue.mod_len(self.state.val().tail))]
        #[invariant(*f == Some(*f_snap))]
        loop {
            let mut perm: Ghost<Option<PermPCell<T>>> = ghost!(None);

            let head = queue.head.load(Ordering::Acquire, ghost! { |c: &Committer<_, _, Acquire, _>| {
                queue.inv.open(tokens.reborrow(), |inv: &mut QueueInv<T>| {
                    inv.consumer_auth.agree(&self.state);
                    c.shoot_load(&inv.head_own, &mut self.view);
                    let t = snapshot!(inv.tail());
                    if c.val_load() != self.tail {
                        // update consumer state from Idle to Consuming
                        let new_state = snapshot!(ConsumerState { tail: *t, view: *self.view, consuming: true });
                        inv.consumer_auth.update(&mut self.state, new_state);
                        // remove (initialized) permission for tail cell
                        let p = inv.cell_perms.delete(&*snapshot!(*t).into_ghost()).unwrap();
                        *perm = Some(p.sync(*self.view));

                        // linearization point: the oldest element is removed from the queue
                        let old_seq = snapshot!(inv.seq());
                        let new_seq = snapshot!(old_seq.tail());
                        f.take().unwrap()(&mut QueueCommitter {
                            auth: &mut inv.contents_auth,
                            id: snapshot!(queue.id()),
                            old_seq,
                            new_seq,
                            shot: false,
                        });
                        proof_assert!(exists<qc: &mut QueueCommitter<T>>
                            !qc.shot() && qc.id() == queue.id() &&
                            qc.old_seq().len() > 0 && qc.new_seq() == qc.old_seq().tail() &&
                            (*f_snap).postcondition_once((qc,), ()) &&
                            perm.unwrap_logic().val()@ == Some(qc.old_seq()[0]));
                    } else {
                        // update consumer view in the invariant
                        let new_state = snapshot!(ConsumerState { tail: *t, view: *self.view, consuming: false });
                        inv.consumer_auth.update(&mut self.state, new_state);
                    }
                })
            }});

            if head != self.tail {
                let item = unsafe {
                    replace(
                        queue.buffer[self.tail].borrow_mut(ghost!(perm.as_mut().unwrap())),
                        MaybeUninit::uninit(),
                    )
                    .assume_init()
                };

                queue.tail.store(
                    next,
                    Ordering::Release,
                    ghost! { |c: &mut Committer<_, _, _, Release>| {
                        queue.inv.open(tokens.reborrow(), |inv: &mut QueueInv<T>| {
                            inv.consumer_auth.agree(&self.state);
                            let t = snapshot!(inv.tail());
                            let old_inv = snapshot!(*inv);

                            // store subjective cell permission at the thread's new view
                            let (mut new_view, at_view) = AtView::new(ghost!(perm.take().unwrap())).into_inner();
                            new_view.join_in(*self.view);
                            c.shoot_store(&mut inv.tail_own, &mut new_view);
                            *self.view = new_view;

                            // update consumer state from Consuming to Idle
                            let new_state = snapshot!(ConsumerState { tail: *t + 1, view: *self.view, consuming: false });
                            inv.consumer_auth.update(&mut self.state, new_state);

                            // insert (uninitialized) permission for (old) tail cell
                            let key = *snapshot!(*t + inv.len()).into_ghost();
                            inv.cell_perms.insert(key, at_view);
                            // update logical value of the new message
                            inv.tail_logical = snapshot!(inv.tail_logical.set(c.timestamp() + 1, *t + 1));
                            snapshot!(inv.mod_len_wrap(*t));
                            proof_assert!(forall<i> inv.mod_len(i) == old_inv.mod_len(i));
                        })
                    }},
                );
                self.tail = next;
                return item;
            }
        }
    }
}

#[requires(tokens.wf(*queue))]
#[ensures(result.0.queue_id() == queue.id())]
#[ensures(result.1.queue_id() == queue.id())]
pub fn channel<'a, T>(
    queue: &'a Queue<T>,
    tokens: Ghost<QueueTokens>,
) -> (Producer<'a, T>, Consumer<'a, T>) {
    let view = ghost!(tokens.view);
    let (producer, consumer) = ghost! {
        let QueueTokens { producer, consumer, .. } = tokens.into_inner();
        (producer, consumer)
    }
    .split();

    let prod = Producer { queue, head: 0, state: producer, view };
    let cons = Consumer { queue, tail: 0, state: consumer, view };
    (prod, cons)
}
