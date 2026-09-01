//! This implementation is an adaption from:
//! https://sites.google.com/site/1024cores/home/lock-free-algorithms/queues/bounded-mpmc-queue

#![recursion_limit = "256"]

use core::{cmp::Ordering, mem::MaybeUninit};
use creusot_std::{
    cell::PermCell,
    ghost::{
        FnGhost,
        invariant::{AtomicInvariant, Protocol, Tokens, declare_namespace},
        perm::Perm,
    },
    logic::{Id, ra::lattice::SemiLattice},
    partial_ord_laws_impl,
    prelude::*,
    std::sync::{
        atomic::{
            AtomicUsize,
            ordering::{self, Acquire, Relaxed, Release},
        },
        committer::Committer,
        view::{AtView, ReleaseSyncView, SyncView, Timestamp},
    },
};

#[cfg(creusot)]
use creusot_std::logic::such_that;

declare_namespace! { BOUNDED_MPMC_QUEUE }

struct StatusWithView {
    status: Int,
    view: SyncView,
}

impl PartialOrdLogic for StatusWithView {
    #[logic]
    fn lt_log(self, other: Self) -> bool {
        (self.status < other.status) || (self.status == other.status && self.view > other.view)
    }

    partial_ord_laws_impl! {}
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

mod state {
    use creusot_std::{
        ghost::resource,
        logic::{Id, ra::excl::Excl},
        prelude::*,
    };

    type ValueRA<T> = Option<Excl<(Seq<T>, Int)>>;

    pub struct Authority<T>(resource::Authority<ValueRA<T>>);
    pub struct Fragment<T>(resource::Fragment<ValueRA<T>>);

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
        pub fn seq(self) -> Seq<T> {
            self.0.view().unwrap_logic().0.0
        }

        #[logic]
        pub fn budget(self) -> Int {
            self.0.view().unwrap_logic().0.1
        }

        #[check(ghost)]
        #[ensures(result.0.id() == result.1.id())]
        #[ensures(*seq == result.0.seq() && budget == result.0.budget())]
        #[ensures(*seq == result.1.seq() && budget == result.1.budget())]
        pub fn alloc(seq: Snapshot<Seq<T>>, budget: Int) -> Ghost<(Authority<T>, Fragment<T>)> {
            ghost! {
                let mut auth = resource::Authority::alloc().into_inner();
                let frag = auth.add_fragment(snapshot!(Some(Excl((*seq, budget)))));

                (Authority(auth), Fragment(frag))
            }
        }

        #[check(ghost)]
        #[requires((*self).id() == (*frag).id())]
        #[ensures((*self).id() == (^self).id())]
        #[ensures((*frag).id() == (^frag).id())]
        #[ensures((*self).seq() == (*frag).seq() && (*self).budget() == (*frag).budget())]
        #[ensures((^self).seq() == *seq && (^self).budget() == *budget)]
        #[ensures((^frag).seq() == *seq && (^frag).budget() == *budget)]
        pub fn update(
            &mut self,
            frag: &mut Fragment<T>,
            seq: Snapshot<Seq<T>>,
            budget: Snapshot<Int>,
        ) {
            let upd = snapshot!(Some(Excl((*seq, *budget))));
            self.0.update(&mut frag.0, snapshot!((*upd, *upd)));
        }
    }

    impl<T> Fragment<T> {
        #[logic]
        pub fn id(self) -> Id {
            self.0.id()
        }

        #[logic]
        pub fn seq(self) -> Seq<T> {
            self.0.view().unwrap_logic().0.0
        }

        #[logic]
        pub fn budget(self) -> Int {
            self.0.view().unwrap_logic().0.1
        }
    }
}

mod statuses {
    use crate::StatusWithView;
    use creusot_std::{
        ghost::resource::{self, Resource},
        logic::{Id, ra::auth::Auth},
        prelude::*,
    };

    pub struct Authority(resource::Authority<Option<StatusWithView>>);
    pub struct Fragment(resource::Fragment<Option<StatusWithView>>);

    impl Invariant for Authority {
        #[logic(inline)]
        fn invariant(self) -> bool {
            self.0.view() != None
        }
    }

    impl Invariant for Fragment {
        #[logic(inline)]
        fn invariant(self) -> bool {
            self.0.view() != None
        }
    }

    impl Authority {
        #[logic]
        pub fn id(self) -> Id {
            self.0.id()
        }

        #[logic]
        pub fn val(self) -> StatusWithView {
            self.0.view().unwrap_logic()
        }

        #[check(ghost)]
        #[ensures(result.val() == *value)]
        pub fn alloc(value: Snapshot<StatusWithView>) -> Ghost<Authority> {
            let resource = Resource::alloc(snapshot!(Auth::new_auth(Some(*value))));
            ghost!(Authority(resource::Authority::from_resource(resource.into_inner()).0))
        }

        #[check(ghost)]
        #[requires(self.id() == frag.id())]
        #[ensures(frag.val() <= self.val())]
        pub fn frag_lemma(&self, frag: &Fragment) {
            self.0.frag_lemma(&frag.0);
        }

        #[check(ghost)]
        #[requires(*value <= self.val())]
        #[ensures((*self).id() == (^self).id())]
        #[ensures((*self).val() == (^self).val())]
        #[ensures(result.id() == (*self).id())]
        #[ensures(result.val() == *value)]
        pub fn get_fragment(&mut self, value: Snapshot<StatusWithView>) -> Fragment {
            Fragment(self.0.add_fragment(snapshot!(Some(*value))))
        }

        #[check(ghost)]
        #[requires(self.val() <= *value)]
        #[ensures((*self).id() == (^self).id())]
        #[ensures((^self).val() == *value)]
        pub fn increase(&mut self, value: Snapshot<StatusWithView>) {
            self.0.add_fragment(snapshot!(Some(*value)));
        }
    }

    impl Fragment {
        #[logic]
        pub fn id(self) -> Id {
            self.0.id()
        }

        #[logic]
        pub fn val(self) -> StatusWithView {
            self.0.view().unwrap_logic()
        }
    }
}

mod tokens {
    use creusot_std::{
        ghost::resource::{self, Resource},
        logic::{
            FMap, Id,
            ra::{
                auth::{Auth, CancelLocalUpdateUnit},
                excl::Excl,
            },
        },
        prelude::*,
    };

    pub struct Authority<T>(resource::Authority<FMap<Int, Excl<Option<T>>>>);
    pub struct TokenR<T>(resource::Fragment<FMap<Int, Excl<Option<T>>>>, Int);
    pub struct TokenW<T>(resource::Fragment<FMap<Int, Excl<Option<T>>>>, Int);

    pub enum State<T> {
        R,
        W(T),
        None,
    }

    impl<T> Invariant for TokenR<T> {
        #[logic(inline)]
        fn invariant(self) -> bool {
            self.0.view() == FMap::singleton(self.1, Excl(None))
        }
    }

    impl<T> Invariant for TokenW<T> {
        #[logic(inline)]
        fn invariant(self) -> bool {
            pearlite! {
                exists<value> self.0.view() == FMap::singleton(self.1, Excl(Some(value)))
            }
        }
    }

    impl<T> Authority<T> {
        #[logic]
        pub fn id(self) -> Id {
            self.0.id()
        }

        #[logic]
        pub fn val(self, idx: Int) -> State<T> {
            match self.0.view().get(idx) {
                None => State::None,
                Some(Excl(None)) => State::R,
                Some(Excl(Some(data))) => State::W(data),
            }
        }

        #[check(ghost)]
        #[ensures(forall<i> result.val(i) == State::None)]
        pub fn alloc() -> Ghost<Authority<T>> {
            let resource = Resource::alloc(snapshot!(Auth::new_auth(FMap::empty())));
            ghost!(Authority(resource::Authority::from_resource(resource.into_inner()).0))
        }
    }

    impl<T> TokenR<T> {
        #[logic]
        pub fn id(self) -> Id {
            self.0.id()
        }

        #[logic]
        pub fn index(self) -> Int {
            self.1
        }

        #[check(ghost)]
        #[requires((*auth).val(index) == State::None)]
        #[ensures((*auth).id() == (^auth).id())]
        #[ensures((^auth).val(index) == State::R)]
        #[ensures(result.index() == index)]
        #[ensures(result.id() == auth.id())]
        #[ensures(forall<i> i != index ==> (*auth).val(i) == (^auth).val(i))]
        pub fn alloc(mut auth: Ghost<&mut Authority<T>>, index: Int) -> Ghost<TokenR<T>> {
            ghost!(TokenR(
                auth.0.add_fragment(snapshot!(FMap::singleton(index, Excl(None)))),
                index
            ))
        }

        #[check(ghost)]
        #[requires(this.id() == (*auth).id())]
        #[ensures((*auth).id() == (^auth).id())]
        #[ensures((*auth).val(this.index()) == State::R)]
        #[ensures((^auth).val(this.index()) == State::None)]
        #[ensures(forall<i> i != this.index() ==> (*auth).val(i) == (^auth).val(i))]
        pub fn discard(this: Ghost<Self>, mut auth: Ghost<&mut Authority<T>>) {
            ghost! {
                let mut frag = this.into_inner().0;
                auth.0.update(&mut frag, CancelLocalUpdateUnit);
            };
        }
    }

    impl<T> TokenW<T> {
        #[logic]
        pub fn id(self) -> Id {
            self.0.id()
        }

        #[logic]
        pub fn val(self) -> T {
            self.0.view()[self.1].0.unwrap_logic()
        }

        #[logic]
        pub fn index(self) -> Int {
            self.1
        }

        #[check(ghost)]
        #[requires((*auth).val(index) == State::None)]
        #[ensures((*auth).id() == (^auth).id())]
        #[ensures((^auth).val(index) == State::W(*value))]
        #[ensures(result.index() == index)]
        #[ensures(result.id() == auth.id())]
        #[ensures(result.val() == *value)]
        #[ensures(forall<i> i != index ==> (*auth).val(i) == (^auth).val(i))]
        pub fn alloc(
            mut auth: Ghost<&mut Authority<T>>,
            index: Int,
            value: Snapshot<T>,
        ) -> Ghost<TokenW<T>> {
            ghost!(TokenW(
                auth.0.add_fragment(snapshot!(FMap::singleton(index, Excl(Some(*value))))),
                index
            ))
        }

        #[check(ghost)]
        #[requires(this.id() == (*auth).id())]
        #[ensures((*auth).id() == (^auth).id())]
        #[ensures((*auth).val(this.index()) == State::W(this.val()))]
        #[ensures((^auth).val(this.index()) == State::None)]
        #[ensures(forall<i> i != this.index() ==> (*auth).val(i) == (^auth).val(i))]
        pub fn discard(this: Ghost<Self>, mut auth: Ghost<&mut Authority<T>>) {
            ghost! {
                let mut frag = this.into_inner().0;
                auth.0.update(&mut frag, CancelLocalUpdateUnit);
            };
        }
    }
}

type PermPermCell<T> = Perm<PermCell<MaybeUninit<T>>>;

pub struct PermQueue<T> {
    fragment: state::Fragment<T>,
    ward: Snapshot<Queue<T>>,
}

impl<T> PermQueue<T> {
    #[logic]
    fn ward(self) -> Queue<T> {
        *self.ward
    }

    #[logic]
    fn budget(self) -> Int {
        self.fragment.budget()
    }
}

impl<T> View for PermQueue<T> {
    type ViewTy = Seq<T>;

    #[logic]
    fn view(self) -> Self::ViewTy {
        self.fragment.seq()
    }
}

impl<T> Invariant for PermQueue<T> {
    #[logic(inline)]
    fn invariant(self) -> bool {
        self.ward.inv.public().3 == self.fragment.id()
    }
}

struct QueueInv<T> {
    head_own: Perm<AtomicUsize>,
    tail_own: Perm<AtomicUsize>,
    cells_own: Seq<Option<AtView<PermPermCell<T>>>>, // in [0; N]
    statuses_own: Seq<Perm<AtomicUsize>>,            // in [0; N]

    values_auth: state::Authority<T>,
    statuses_mono_auth: Seq<statuses::Authority>, // in [0; N]
    tokens_auth: tokens::Authority<T>,

    head_last_ts: Timestamp,
    tail_last_ts: Timestamp,

    cells: Snapshot<Seq<QueueCell<T>>>,
    statuses_mono_auth_wards: Snapshot<Seq<Id>>,
}

impl<T> QueueInv<T> {
    #[logic]
    fn len(self) -> Int {
        self.cells.len()
    }

    #[logic]
    fn head(self) -> Int {
        self.head_own.val()[self.head_last_ts].0.view()
    }

    #[logic]
    fn tail(self) -> Int {
        self.tail_own.val()[self.tail_last_ts].0.view()
    }

    #[logic]
    fn seq(self) -> Seq<T> {
        self.values_auth.seq()
    }

    #[logic]
    fn mod_len(self, i: Int) -> Int {
        i.rem_euclid(self.len())
    }

    #[logic(opaque)]
    #[requires(self.mod_len(i) == self.mod_len(j))]
    #[requires(-self.len() < i - j && i - j < self.len())]
    #[ensures(i == j)]
    fn mod_len_inj(self, i: Int, j: Int) {}

    #[logic(opaque)]
    #[ensures(self.mod_len(i + self.len()) == self.mod_len(i))]
    fn mod_len_wrap(self, i: Int) {}
}

impl<T> Protocol for QueueInv<T> {
    type Public = (AtomicUsize, AtomicUsize, Seq<QueueCell<T>>, Id, Seq<Id>, Id);

    #[logic]
    fn public(self) -> Self::Public {
        (
            *self.head_own.ward(),
            *self.tail_own.ward(),
            *self.cells,
            self.values_auth.id(),
            *self.statuses_mono_auth_wards,
            self.tokens_auth.id(),
        )
    }

    #[logic(inline)]
    fn protocol(self) -> bool {
        pearlite! {
            self.len() > 0 &&
            self.len() == self.cells_own.len() &&
            self.len() == self.statuses_own.len() &&
            self.len() == self.statuses_mono_auth.len() &&

            self.values_auth.budget() == usize::MAX@ - 2*self.len() + 1 - self.head() - self.tail() &&
            self.values_auth.budget() >= 0 &&

            (forall<i> 0 <= i && i < self.len() ==>
                match self.cells_own[i] {
                    Some(at_view) => *at_view.val().ward() == self.cells[i].item,
                    _ => true
                }) &&

            (forall<i> 0 <= i && i < self.len() ==>
                *self.statuses_own[i].ward() == self.cells[i].status) &&

            (self.len() == self.statuses_mono_auth_wards.len()) &&
            (forall<i> 0 <= i && i < self.len() ==>
                self.statuses_mono_auth[i].id() == self.statuses_mono_auth_wards[i]) &&

            // 0 <= t <= h <= t + len
            (0 <= self.tail() && self.tail() <= self.head() && self.head() <= self.tail() + self.len()) &&

            // head ~> (h, H)
            (forall<ts> #[trigger(self.head_own.val().get(ts))]
                match self.head_own.val().get(ts) {
                    Some((h, _)) =>
                        ts == self.head_last_ts ||
                        self.head_own.val().contains(ts + 1) &&
                        h@ < self.head(),
                    None => true
                }
            ) &&

            // tail ~> (t, T)
            (forall<ts> #[trigger(self.tail_own.val().get(ts))]
                match self.tail_own.val().get(ts) {
                    Some((t, _)) =>
                        ts == self.tail_last_ts ||
                        self.tail_own.val().contains(ts + 1) &&
                        t@ < self.tail(),
                    None => true
                }
            ) &&

            // statuses ~>* [(s_0, S_0), ..., (s_len - 1, S_len - 1)]
            // { i -> •(s_i, S_i) | 0 <= i < len }
            (forall<i: Int, ts: Int> #[trigger(self.statuses_own[i].val().get(ts))]
                 0 <= i && i < self.len() ==>
                 match self.statuses_own[i].val().get(ts) {
                     Some((status, view)) => StatusWithView { status: status@, view } <= self.statuses_mono_auth[i].val(),
                     _ => true
                 }) &&

            // • [(v_t, V_t), ..., (v_h-1, V_h-1)]
            self.seq().len() == self.head() - self.tail() &&

            (forall<k: Int> #[trigger(self.tokens_auth.val(k))] self.tail() <= k && k < self.tail() + self.len() ==> {
                let status_view = self.statuses_mono_auth[self.mod_len(k)].val();
                match self.tokens_auth.val(k) {
                    tokens::State::R => status_view.status == 2 * (k - self.len()) + 1 && self.head() <= k,
                    tokens::State::W(value) => status_view.status == 2 * k && k < self.head() && value == self.seq()[k - self.tail()],
                    tokens::State::None =>
                        match self.cells_own[self.mod_len(k)] {
                            Some(at_view) =>
                                status_view.view >= at_view.view() &&
                                if self.head() <= k { status_view.status == 2 * k }
                                else { status_view.status == 2 * k + 1 && at_view.val().val()@ == Some(self.seq()[k - self.tail()]) },
                            _ => false
                        }
                }
            }) &&

            // *{0 < k < h - len && h <= k} None
            (forall<k: Int> k < self.tail() || self.tail() + self.len() <= k ==> self.tokens_auth.val(k) == tokens::State::None)
        }
    }
}

pub struct Queue<T> {
    cells: Vec<QueueCell<T>>,
    head: AtomicUsize,
    tail: AtomicUsize,
    inv: Ghost<AtomicInvariant<QueueInv<T>>>,
}

struct QueueCell<T> {
    item: PermCell<MaybeUninit<T>>,
    status: AtomicUsize,
}

impl<T> Invariant for Queue<T> {
    #[logic(inline)]
    fn invariant(self) -> bool {
        pearlite! {
            let (head, tail, cells, _, _, _) = self.inv.public();
            head == self.head &&
            tail == self.tail &&
            cells == self.cells@ &&
            self.inv.namespace() == BOUNDED_MPMC_QUEUE()
        }
    }
}

pub struct QueueCommitter<'a, T> {
    auth: &'a mut state::Authority<T>,
    budget: Int,

    ward: Snapshot<Queue<T>>,
    old_seq: Snapshot<Seq<T>>,
    new_seq: Snapshot<Seq<T>>,
    shot: bool,
}

impl<T> Invariant for QueueCommitter<'_, T> {
    #[logic(inline)]
    fn invariant(self) -> bool {
        self.auth.id() == self.ward.inv.public().3
            && if self.shot {
                self.auth.seq() == *self.new_seq
                    && self.auth.budget() == self.budget - 1
                    && self.auth.budget() >= 0
            } else {
                self.auth.seq() == *self.old_seq && self.auth.budget() == self.budget
            }
    }
}

impl<T> QueueCommitter<'_, T> {
    #[requires(!(*self).shot)]
    #[requires(*self.ward == perm.ward())]
    #[requires((*perm).budget() > 0)]
    #[ensures((^self).shot)]
    #[ensures((*self).hist_inv(^self))]
    #[ensures((*perm)@ == *self.old_seq)]
    #[ensures((^perm)@ == *self.new_seq)]
    #[ensures((^perm).ward() == (*perm).ward())]
    #[ensures((^perm).budget() == (*perm).budget()-1)]
    #[check(ghost)]
    pub fn shoot(&mut self, perm: &mut PermQueue<T>) {
        let budget = snapshot!(self.budget - 1);
        self.auth.update(&mut perm.fragment, self.new_seq, budget);
        self.shot = true;
    }

    #[logic(inline, prophetic)]
    pub fn hist_inv(self, other: Self) -> bool {
        pearlite! {
            self.ward == other.ward && ^self.auth == ^other.auth &&
            self.old_seq == other.old_seq && self.new_seq == other.new_seq &&
            self.budget == other.budget
        }
    }
}

impl<T> Queue<T> {
    #[requires(0 < 2 * length@ && 2 * length@ <= usize::MAX@)]
    #[ensures(result.0 == result.1.ward())]
    #[ensures(result.1@ == Seq::empty())]
    #[ensures(result.1.budget() == usize::MAX@ - 2 * length@ + 1)]
    pub fn new(length: usize) -> (Self, Ghost<PermQueue<T>>) {
        let tokens_auth: Ghost<tokens::Authority<T>> = tokens::Authority::alloc();
        let mut statuses_mono_auth: Ghost<Seq<statuses::Authority>> = Seq::new();
        let mut cells_own: Ghost<Seq<Option<AtView<PermPermCell<T>>>>> = Seq::new();
        let mut statuses_own: Ghost<Seq<Perm<AtomicUsize>>> = Seq::new();
        let mut cells: Vec<QueueCell<T>> = Vec::new();

        #[invariant(cells@.len() == produced.len())]
        #[invariant(cells_own.len() == produced.len())]
        #[invariant(statuses_mono_auth.len() == produced.len())]
        #[invariant(statuses_own.len() == produced.len())]
        #[invariant(forall<i> 0 <= i && i < produced.len() ==>
             match cells_own[i] {
                 Some(at_view) => *at_view.val().ward() == cells@[i].item,
                 None => false
             }
        )]
        #[invariant(forall<i> produced.len() <= i ==> statuses_mono_auth.get(i) == None)]
        #[invariant(forall<i> 0 <= i && i < produced.len() ==> *statuses_own[i].ward() == cells@[i].status)]
        #[invariant(forall<i> 0 <= i && i < produced.len() ==>
             forall<ts>
             match statuses_own[i].val().get(ts) {
                 Some((status, view)) => StatusWithView { status: status@, view } <= statuses_mono_auth[i].val(),
                 _ => true
             }
        )]
        #[invariant(forall<i: Int> #[trigger(statuses_mono_auth[i.rem_euclid(length@)].val())] 0 <= i && i < produced.len() ==>
             match statuses_mono_auth[i.rem_euclid(length@)].val() {
                 StatusWithView { status, view } =>
                     status == 2 * i && match cells_own[i] {
                         Some(at_view) => view >= at_view.view(),
                         None => false,
                     }
             }
        )]
        for i in 0..length {
            let (item, item_own) = PermCell::new(MaybeUninit::uninit());

            let at_view = AtView::new(item_own);
            let mut view = ghost!(at_view.0);
            let at_view = ghost!(at_view.into_inner().1);

            let (status, status_own) = AtomicUsize::new(2 * i, view.borrow_mut());

            ghost! {
                cells_own.push_back_ghost(Some(at_view.into_inner()));
                statuses_own.push_back_ghost(status_own.into_inner());

                let status = snapshot!(StatusWithView { status: 2 * i@, view: *view });
                statuses_mono_auth.push_back_ghost(statuses::Authority::alloc(status).into_inner());
            };

            cells.push(QueueCell { item, status })
        }

        let (head, head_own) = AtomicUsize::new(0, SyncView::new().borrow_mut());
        let head_ts = snapshot!(such_that(|t| head_own.val().contains(t)));
        let (tail, tail_own) = AtomicUsize::new(0, SyncView::new().borrow_mut());
        let tail_ts = snapshot!(such_that(|t| tail_own.val().contains(t)));

        let statuses_mono_auth_wards =
            snapshot!(statuses_mono_auth.map(|x: statuses::Authority| x.id()));

        let (values_auth, values_frag) = ghost!(
            state::Authority::alloc(
                snapshot!(Seq::empty()),
                *snapshot!(usize::MAX@ - 2 * length@ + 1).into_ghost()
            )
            .into_inner()
        )
        .split();

        let inv = AtomicInvariant::new(
            ghost!(QueueInv {
                head_own: head_own.into_inner(),
                tail_own: tail_own.into_inner(),
                cells_own: cells_own.into_inner(),
                statuses_own: statuses_own.into_inner(),

                values_auth: values_auth.into_inner(),
                statuses_mono_auth: statuses_mono_auth.into_inner(),
                tokens_auth: tokens_auth.into_inner(),

                head_last_ts: *head_ts.into_ghost(),
                tail_last_ts: *tail_ts.into_ghost(),

                cells: snapshot!(cells@),
                statuses_mono_auth_wards,
            }),
            snapshot!(BOUNDED_MPMC_QUEUE()),
        );

        let queue = Queue { cells, head, tail, inv };

        let perm_queue =
            ghost!(PermQueue { fragment: values_frag.into_inner(), ward: snapshot!(queue) });

        (queue, perm_queue)
    }

    #[check(ghost)]
    // Invariant requires/ensures
    #[requires((*inv).protocol())]
    #[requires(self.inv.public() == (*inv).public())]
    #[ensures((^inv).protocol())]
    #[ensures(self.inv.public() == (^inv).public())]
    // Committer
    #[requires(!c.shot_store())]
    #[requires(c.ward() == *inv.head_own.ward())]
    #[requires(c.val_store()@ == c.val_load()@ + 1)]
    #[ensures((^c).shot_store())]
    // Invariant
    #[requires(witness.id() == inv.statuses_mono_auth[inv.mod_len(c.val_load()@)].id())]
    #[requires(StatusWithView { status: 2 * c.val_load()@, view: *view } <= witness.val())]
    #[ensures(result.0.id() == inv.tokens_auth.id())]
    #[ensures(result.0.val() == *item)]
    #[ensures(result.0.index() == c.val_load()@)]
    #[ensures(*result.1.ward() == inv.cells[inv.mod_len(result.0.index())].item)]
    // User committer
    #[requires(forall<c: &mut QueueCommitter<T>>
        !c.shot ==> *c.ward == *self ==>
        *c.new_seq == c.old_seq.push_back(*item) ==>
            f.precondition((c,)) && (f.postcondition_once((c,),()) ==> (^c).shot && (*c).hist_inv(^c))
    )]
    #[ensures(exists<c: &mut QueueCommitter<T>>
        !c.shot && *c.ward == *self &&
        *c.new_seq == c.old_seq.push_back(*item) && f.postcondition_once((c,),())
    )]
    fn try_enqueue_cas_inv<F>(
        &self,
        mut inv: Ghost<&mut QueueInv<T>>,
        mut c: Ghost<&mut Committer<AtomicUsize, usize, Relaxed, Relaxed>>,
        item: Snapshot<T>,
        f: Ghost<F>,
        witness: statuses::Fragment,
        mut view: Ghost<SyncView>,
    ) -> Ghost<(tokens::TokenW<T>, PermPermCell<T>)>
    where
        F: FnGhost + FnOnce(&mut QueueCommitter<T>),
    {
        ghost! {
            let inv = &mut **inv;
            let head = snapshot!(inv.head());
            let head_mod = *snapshot!(inv.mod_len(*head)).into_ghost();

            c.shoot_load(&inv.head_own, &mut view);
            c.shoot_store(
                &mut inv.head_own,
                &mut view,
                *ReleaseSyncView::new(),
            );
            inv.head_last_ts += 1int;
            proof_assert!(c.val_load()@ == *head);

            inv.statuses_mono_auth[head_mod].frag_lemma(&witness);

            proof_assert!(inv.tokens_auth.val(*head) == tokens::State::None);
            proof_assert!(inv.tokens_auth.val(*head - inv.len()) == tokens::State::None);
            proof_assert!(*head < inv.tail() + inv.len());

            let old_seq = snapshot!(inv.seq());
            let new_seq = snapshot!(old_seq.push_back(*item));
            let budget = *snapshot!(inv.values_auth.budget()).into_ghost();
            f.into_inner()(&mut QueueCommitter {
                auth: &mut inv.values_auth,
                ward: snapshot!(*self),
                old_seq,
                new_seq,
                shot: false,
                budget
            });

            let cell_own = inv.cells_own[head_mod].take().unwrap().sync(*view);

            let token = tokens::TokenW::alloc(
                Ghost::new(&mut inv.tokens_auth),
                *head.into_ghost(),
                item,
            );

            (token.into_inner(), cell_own)
        }
    }

    #[check(ghost)]
    // Invariant requires/ensures
    #[requires((*inv).protocol())]
    #[ensures((^inv).protocol())]
    #[ensures((^inv).public() == (*inv).public())]
    // Committer
    #[requires(!c.shot_store())]
    #[requires(c.ward() == *inv.statuses_own[inv.mod_len(token.index())].ward())]
    #[requires(c.val_store()@ == 2 * token.index() + 1)]
    #[ensures((^c).shot_store())]
    // Invariant
    #[requires(token.id() == inv.tokens_auth.id())]
    #[requires(cell_own.val()@ == Some(token.val()))]
    #[requires(*cell_own.ward() == inv.cells[inv.mod_len(token.index())].item)]
    fn try_enqueue_store_inv(
        mut inv: Ghost<&mut QueueInv<T>>,
        mut c: Ghost<&mut Committer<AtomicUsize, usize, ordering::None, Release>>,
        token: Ghost<tokens::TokenW<T>>,
        cell_own: Ghost<PermPermCell<T>>,
    ) {
        ghost! {
            let inv = &mut **inv;
            let index_mod = *snapshot!(inv.mod_len(token.index())).into_ghost();

            let (mut view, at_view) = AtView::new(cell_own).into_inner();
            c.shoot_store(&mut inv.statuses_own[index_mod], &mut view);

            tokens::TokenW::discard(token, Ghost::new(&mut inv.tokens_auth));

            let status_view = snapshot!(StatusWithView { status: c.val_store()@, view });
            inv.statuses_mono_auth[index_mod].increase(status_view);

            inv.cells_own[index_mod] = Some(at_view);

            let _ = snapshot!(QueueInv::<T>::mod_len_inj);
        };
    }

    #[requires(tokens.contains(BOUNDED_MPMC_QUEUE()))]
    #[requires(forall<c: &mut QueueCommitter<T>>
        !c.shot ==> *c.ward == *self ==>
        *c.new_seq == c.old_seq.push_back(item) ==>
        f.precondition((c,)) && (f.postcondition_once((c,),()) ==> (^c).shot && (*c).hist_inv(^c))
    )]
    #[ensures(result ==> exists<c: &mut QueueCommitter<T>>
        !c.shot && *c.ward == *self &&
        *c.new_seq == c.old_seq.push_back(item) && f.postcondition_once((c,),())
    )]
    #[ensures(!result ==> resolve(f))]
    pub fn try_enqueue<F>(&self, item: T, mut tokens: Ghost<Tokens>, f: Ghost<F>) -> bool
    where
        F: FnGhost + FnOnce(&mut QueueCommitter<T>),
    {
        let mut view = SyncView::new();
        let mut witness: Ghost<Option<statuses::Fragment>> = ghost!(None);

        let head = self.head.load(ghost! { |c: &Committer<_, _, Relaxed, _>| {
            self.inv.open(tokens.reborrow(), |inv: &mut QueueInv<T>| {
                c.shoot_load(&inv.head_own, &mut SyncView::new());
            });
        } });

        let head_mod = head % self.cells.len();
        proof_assert!(head_mod@ == head@.rem_euclid(self.cells@.len()));

        let cell = &self.cells[head_mod];
        let status = cell.status.load(ghost! { |c: &Committer<_, _, Acquire, _>| {
            self.inv.open(tokens.reborrow(), |inv: &mut QueueInv<T>| {
                let head_mod_ghost: Ghost<Int> = snapshot!(head_mod@).into_ghost();
                c.shoot_load(&inv.statuses_own[*head_mod_ghost], &mut view.borrow_mut());

                let status_view = snapshot!(StatusWithView { status: c.val_load()@, view: *view });
                *witness = Some(inv.statuses_mono_auth[*head_mod_ghost].get_fragment(status_view));
            });
        } });

        if 2 * head != status {
            return false;
        }

        let mut token: Ghost<Option<tokens::TokenW<T>>> = ghost!(None);
        let mut cell_own: Ghost<Option<PermPermCell<T>>> = ghost!(None);
        let res = self.head.compare_exchange_weak::<_, Relaxed, Relaxed>(
            head,
            head + 1,
            ghost! { |c: Result<&mut Committer<_, _, Relaxed, Relaxed>, &_>| {
                let Ok(c) = c else { return; };

                self.inv.open(tokens.reborrow(), |inv: &mut QueueInv<T>| {
                    let item_snap = snapshot!(item);
                    let (t, co) = self.try_enqueue_cas_inv(
                        Ghost::new(inv),
                        Ghost::new(c),
                        item_snap,
                        f,
                        witness.take().unwrap(),
                        view
                    ).into_inner();

                    *token = Some(t);
                    *cell_own = Some(co);
                });
            }},
        );

        if res.is_err() {
            return false;
        }

        unsafe { cell.item.set(ghost!(cell_own.as_mut().unwrap()), MaybeUninit::new(item)) };

        cell.status.store(
            2 * head + 1,
            ghost! { |c: &mut Committer<_, _, _, Release>| {
                self.inv.open(tokens.reborrow(), |inv: &mut QueueInv<T>| {
                    Self::try_enqueue_store_inv(
                        Ghost::new(inv),
                        Ghost::new(c),
                        Ghost::new(token.take().unwrap()),
                        Ghost::new(cell_own.take().unwrap()),
                    )
                });
            }},
        );

        true
    }

    #[check(ghost)]
    // Invariant requires/ensures
    #[requires((*inv).protocol())]
    #[requires(self.inv.public() == (*inv).public())]
    #[ensures((^inv).protocol())]
    #[ensures(self.inv.public() == (^inv).public())]
    // Committer
    #[requires(!c.shot_store())]
    #[requires(c.ward() == *inv.tail_own.ward())]
    #[requires(c.val_store()@ == c.val_load()@ + 1)]
    #[ensures((^c).shot_store())]
    // Invariant
    #[requires(witness.id() == inv.statuses_mono_auth[inv.mod_len(c.val_load()@)].id())]
    #[requires(StatusWithView { status: 2 * c.val_load()@ + 1, view: *view } <= witness.val())]
    #[ensures(result.0.id() == inv.tokens_auth.id())]
    #[ensures(result.0.index() == c.val_load()@ + inv.len())]
    #[ensures(*result.1.ward() == inv.cells[inv.mod_len(result.0.index())].item)]
    #[ensures(inv.mod_len(result.0.index()) == inv.mod_len(c.val_load()@))]
    // User committer
    #[requires(forall<c: &mut QueueCommitter<T>>
        !c.shot ==> *c.ward == *self ==>
        c.old_seq.len() > 0 && *c.new_seq == c.old_seq.pop_front() ==>
        f.precondition((c,)) && (f.postcondition_once((c,),()) ==> (^c).shot && (*c).hist_inv(^c))
    )]
    #[ensures(exists<c: &mut QueueCommitter<T>>
        !c.shot && *c.ward == *self &&
        c.old_seq.len() > 0 && *c.new_seq == c.old_seq.pop_front() &&
        f.postcondition_once((c,),()) &&
        result.1.val()@ == Some(c.old_seq[0])
    )]
    #[ensures(2 * (c.val_load()@ + inv.len()) < usize::MAX@)]
    fn try_dequeue_cas_inv<F>(
        &self,
        mut inv: Ghost<&mut QueueInv<T>>,
        mut c: Ghost<&mut Committer<AtomicUsize, usize, Relaxed, Relaxed>>,
        f: Ghost<F>,
        witness: statuses::Fragment,
        mut view: Ghost<SyncView>,
    ) -> Ghost<(tokens::TokenR<T>, PermPermCell<T>)>
    where
        F: FnGhost + FnOnce(&mut QueueCommitter<T>),
    {
        ghost! {
            let inv = &mut **inv;
            let tail = snapshot!(inv.tail());
            let tail_plus_len = snapshot!(*tail + inv.len());
            let tail_mod = *snapshot!(inv.mod_len(*tail)).into_ghost();
            let _ = snapshot!(QueueInv::<T>::mod_len_wrap);
            proof_assert!(tail_mod == inv.mod_len(*tail_plus_len));

            c.shoot_load(&inv.tail_own, &mut view);
            c.shoot_store(
                &mut inv.tail_own,
                &mut view,
                *ReleaseSyncView::new(),
            );
            inv.tail_last_ts += 1int;
            proof_assert!(c.val_load()@ == *tail);

            inv.statuses_mono_auth[tail_mod].frag_lemma(&witness);

            proof_assert!(inv.tokens_auth.val(*tail) == tokens::State::None);
            proof_assert!(*tail < inv.head());

            let old_seq = snapshot!(inv.seq());
            let new_seq = snapshot!(old_seq.pop_front());
            let budget = *snapshot!(inv.values_auth.budget()).into_ghost();
            f.into_inner()(&mut QueueCommitter {
                auth: &mut inv.values_auth,
                ward: snapshot!(*self),
                old_seq,
                new_seq,
                shot: false,
                budget
            });

            let cell_own = inv.cells_own[tail_mod].take().unwrap().sync(*view);

            let token = tokens::TokenR::alloc(
                Ghost::new(&mut inv.tokens_auth),
                *tail_plus_len.into_ghost(),
            );

            (token.into_inner(), cell_own)
        }
    }

    #[check(ghost)]
    // Invariant requires/ensures
    #[requires((*inv).protocol())]
    #[ensures((^inv).protocol())]
    #[ensures((^inv).public() == (*inv).public())]
    // Committer
    #[requires(!c.shot_store())]
    #[requires(c.ward() == *inv.statuses_own[inv.mod_len(token.index())].ward())]
    #[requires(c.val_store()@ == 2 * token.index())]
    #[ensures((^c).shot_store())]
    // Invariant
    #[requires(token.id() == inv.tokens_auth.id())]
    #[requires(*cell_own.ward() == inv.cells[inv.mod_len(token.index())].item)]
    fn try_dequeue_store_inv(
        mut inv: Ghost<&mut QueueInv<T>>,
        mut c: Ghost<&mut Committer<AtomicUsize, usize, ordering::None, Release>>,
        token: Ghost<tokens::TokenR<T>>,
        cell_own: Ghost<PermPermCell<T>>,
    ) {
        ghost! {
            let inv = &mut **inv;
            let index_mod = *snapshot!(inv.mod_len(token.index())).into_ghost();

            let (mut view, at_view) = AtView::new(cell_own).into_inner();
            c.shoot_store(&mut inv.statuses_own[index_mod], &mut view);

            tokens::TokenR::discard(token, Ghost::new(&mut inv.tokens_auth));

            let status_view = snapshot!(StatusWithView { status: c.val_store()@, view });
            inv.statuses_mono_auth[index_mod].increase(status_view);

            inv.cells_own[index_mod] = Some(at_view);

            let _ = snapshot!(QueueInv::<T>::mod_len_inj);
        };
    }

    #[requires(tokens.contains(BOUNDED_MPMC_QUEUE()))]
    #[requires(forall<c: &mut QueueCommitter<T>>
        !c.shot ==> *c.ward == *self ==>
        c.old_seq.len() > 0 && *c.new_seq == c.old_seq.pop_front() ==>
        f.precondition((c,)) && (f.postcondition_once((c,),()) ==> (^c).shot && (*c).hist_inv(^c))
    )]
    #[ensures(match result {
        Some(result) => exists<c: &mut QueueCommitter<T>>
            !c.shot && *c.ward == *self &&
            c.old_seq.len() > 0 && *c.new_seq == c.old_seq.pop_front() &&
            f.postcondition_once((c,),()) &&
            result == c.old_seq[0],
        None => resolve(f)
    })]
    pub fn try_dequeue<F>(&self, mut tokens: Ghost<Tokens>, f: Ghost<F>) -> Option<T>
    where
        F: FnGhost + FnOnce(&mut QueueCommitter<T>),
    {
        let mut view = SyncView::new();
        let mut witness: Ghost<Option<statuses::Fragment>> = ghost!(None);

        let tail = self.tail.load(ghost! { |c: &Committer<_, _, Relaxed, _>| {
            self.inv.open(tokens.reborrow(), |inv: &mut QueueInv<T>| {
                c.shoot_load(&inv.tail_own, &mut SyncView::new());
            });
        } });

        let tail_mod = tail % self.cells.len();
        proof_assert!(tail_mod@ == tail@.rem_euclid(self.cells@.len()));

        let cell = &self.cells[tail_mod];
        let status = cell.status.load(ghost! { |c: &Committer<_, _, Acquire, _>| {
            self.inv.open(tokens.reborrow(), |inv: &mut QueueInv<T>| {
                let tail_mod_ghost: Ghost<Int> = snapshot!(tail_mod@).into_ghost();
                c.shoot_load(&inv.statuses_own[*tail_mod_ghost], &mut view.borrow_mut());

                let status_view = snapshot!(StatusWithView { status: c.val_load()@, view: *view });
                *witness = Some(inv.statuses_mono_auth[*tail_mod_ghost].get_fragment(status_view));
            });
        } });

        if 2 * tail + 1 != status {
            return None;
        }

        let mut token: Ghost<Option<tokens::TokenR<T>>> = ghost!(None);
        let mut cell_own: Ghost<Option<PermPermCell<T>>> = ghost!(None);
        let res = self.tail.compare_exchange_weak::<_, Relaxed, Relaxed>(
            tail,
            tail + 1,
            ghost! { |c: Result<&mut Committer<_, _, Relaxed, Relaxed>, &_>| {
                let Ok(c) = c else { return; };

                self.inv.open(tokens.reborrow(), |inv: &mut QueueInv<T>| {
                   let (t, co) = self.try_dequeue_cas_inv(
                        Ghost::new(inv),
                        Ghost::new(c),
                        f,
                        witness.take().unwrap(),
                        view
                    ).into_inner();

                    *token = Some(t);
                    *cell_own = Some(co);
                });
            }},
        );

        if res.is_err() {
            return None;
        }

        let item = unsafe {
            cell.item
                .replace(ghost!(cell_own.as_mut().unwrap()), MaybeUninit::uninit())
                .assume_init()
        };

        cell.status.store(
            2 * (tail + self.cells.len()),
            ghost! { |c: &mut Committer<_, _, _, Release>| {
                self.inv.open(tokens.reborrow(), |inv: &mut QueueInv<T>| {
                    Self::try_dequeue_store_inv(
                        Ghost::new(inv),
                        Ghost::new(c),
                        Ghost::new(token.take().unwrap()),
                        Ghost::new(cell_own.take().unwrap()),
                    )
                });
            }},
        );

        Some(item)
    }
}

/* Checking whether QueueInv is `Objective` */
#[cfg(creusot)]
#[allow(dead_code)]
fn test() {
    use creusot_std::ghost::Objective;

    fn check_objectivity<T: Objective>() {}
    fn check_send<T: Send>() {}
    fn check_sync<T: Sync>() {}

    fn foo<T: Send>() {
        check_objectivity::<PermQueue<T>>();
        check_send::<PermQueue<T>>();
        check_sync::<PermQueue<T>>();

        check_send::<Queue<T>>();
        check_sync::<Queue<T>>();
    }
}
