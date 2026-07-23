//! This implementation is an adaption from:
//! https://sites.google.com/site/1024cores/home/lock-free-algorithms/queues/bounded-mpmc-queue

#![allow(unused)]

use core::borrow::BorrowMut;
use core::{cmp::Ordering, mem::MaybeUninit};
use creusot_std::{
    cell::PermCell,
    ghost::{
        invariant::{declare_namespace, AtomicInvariant, Protocol, Tokens},
        perm::Perm,
        resource::{Authority, Fragment, Resource},
    },
    logic::{
        ra::{auth::Auth, excl::Excl, lattice::SemiLattice, RA},
        seq::Seq,
        FMap, Id,
    },
    partial_ord_laws_impl,
    prelude::*,
    std::sync::{
        atomic::{
            ordering::{Acquire, Relaxed, Release},
            AtomicUsize,
        },
        committer::Committer,
        view::{AtView, HasTimestamp, ReleaseSyncView, SyncView},
    },
};

declare_namespace! { BOUNDED_MPMC_QUEUE }

#[logic]
#[requires(y > 0)]
#[ensures(x.rem_euclid(y) == (x - y).rem_euclid(y))]
pub fn rem_euclid_minus(x: Int, y: Int) {}

pub struct StatusWithView {
    pub status: Int,
    pub view: SyncView,
}

impl PartialOrdLogic for StatusWithView {
    #[logic(open)]
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
            Ordering::Equal => StatusWithView {
                status: self.status,
                view: self.view.meet(other.view),
            },
        }
    }
}

mod values {
    use creusot_std::{
        ghost::resource::{self, Resource},
        logic::{
            ra::{excl::Excl, update::LocalUpdate, UnitRA, RA},
            Id, Seq,
        },
        prelude::*,
    };

    type ValueRA<T> = Option<Excl<Seq<T>>>;

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
        pub fn val(self) -> Seq<T> {
            self.0.view().unwrap_logic().0
        }

        #[check(ghost)]
        #[ensures(result.0.id() == result.1.id())]
        #[ensures(*value == result.0.val())]
        #[ensures(*value == result.1.val())]
        pub fn alloc(value: Snapshot<Seq<T>>) -> (Ghost<Authority<T>>, Ghost<Fragment<T>>) {
            // TODO: [VL] Use other style, with Auth::new(value, value) instead of Auth::new_auth
            let mut auth = ghost!(resource::Authority::alloc().into_inner());
            let frag = ghost!(auth.add_fragment(snapshot!(Some(Excl(*value)))));

            (
                ghost!(Authority(auth.into_inner())),
                ghost!(Fragment(frag.into_inner())),
            )
        }

        #[check(ghost)]
        #[requires((*self).id() == (*frag).id())]
        #[ensures((*self).id() == (^self).id())]
        #[ensures((*frag).id() == (^frag).id())]
        #[ensures((*self).val() == (*frag).val())]
        #[ensures({
            let result = (*frag).val().push_back(*value);
            (^self).val() == result && (^frag).val() == result
        })]
        pub fn update(&mut self, frag: &mut Fragment<T>, value: Snapshot<T>) {
            // TODO: [VL] push_back/pop_front user
            let upd = snapshot!(Some(Excl(frag.val().push_back(*value))));
            self.0.update(&mut frag.0, snapshot!((*upd, *upd)));
        }
    }

    impl<T> Fragment<T> {
        #[logic]
        pub fn id(self) -> Id {
            self.0.id()
        }

        #[logic]
        pub fn val(self) -> Seq<T> {
            self.0.view().unwrap_logic().0
        }
    }
}

mod statuses {
    use crate::StatusWithView;
    use creusot_std::{
        ghost::resource::{self, Resource},
        logic::{
            ra::{auth::Auth, excl::Excl, update::LocalUpdate, UnitRA, RA},
            Id, Seq,
        },
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
            ghost!(Authority(
                resource::Authority::from_resource(resource.into_inner()).0
            ))
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
            ra::{
                auth::{Auth, CancelLocalUpdateUnit},
                excl::Excl,
                fmap::FMapKeyLocalUpdate,
                update::LocalUpdate,
                UnitRA, RA,
            },
            FMap, Id, Seq,
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
            ghost!(Authority(
                resource::Authority::from_resource(resource.into_inner()).0
            ))
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
                auth.0
                    .add_fragment(snapshot!(FMap::singleton(index, Excl(None)))),
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
            self.0.view().get(self.1).unwrap_logic().0.unwrap_logic()
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
                auth.0
                    .add_fragment(snapshot!(FMap::singleton(index, Excl(Some(*value))))),
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
    fragment: values::Fragment<T>,
    ward: Snapshot<Queue<T>>,
}

impl<T> PermQueue<T> {
    #[logic]
    fn ward(self) -> Queue<T> {
        *self.ward
    }
}

impl<T> View for PermQueue<T> {
    type ViewTy = Seq<T>;

    #[logic]
    fn view(self) -> Self::ViewTy {
        self.fragment.val()
    }
}

impl<T> Invariant for PermQueue<T> {
    #[logic(inline)]
    fn invariant(self) -> bool {
        self.ward.inv.public().4 == self.fragment.id()
    }
}

// TODO: [VL] Check at compile-time that this struct is Objective: No synchronisation required here.
// NOTE: https://users.rust-lang.org/t/testing-if-a-type-is-implementing-an-auto-trait/90871/6
struct QueueInv<T> {
    head_own: Perm<AtomicUsize>,
    tail_own: Perm<AtomicUsize>,
    cells_own: Seq<Option<AtView<PermPermCell<T>>>>, // in [0; N]
    statuses_own: Seq<Perm<AtomicUsize>>,            // in [0; N]

    values_auth: values::Authority<T>,
    statuses_mono_auth: Seq<statuses::Authority>, // in [0; N]
    tokens_auth: tokens::Authority<T>,

    head: Snapshot<Int>,
    tail: Snapshot<Int>,
    values: Snapshot<Seq<T>>, // in [self.tail; self.head - 1]

    cells_wards: Snapshot<Seq<PermCell<MaybeUninit<T>>>>,
    statuses_own_wards: Snapshot<Seq<AtomicUsize>>,
    statuses_mono_auth_wards: Snapshot<Seq<Id>>,
}

impl<T> Protocol for QueueInv<T> {
    type Public = (
        AtomicUsize,
        AtomicUsize,
        Seq<PermCell<MaybeUninit<T>>>,
        Seq<AtomicUsize>,
        Id,
        Seq<Id>,
        Id,
    );

    #[logic]
    fn public(self) -> Self::Public {
        (
            *self.head_own.ward(),
            *self.tail_own.ward(),
            *self.cells_wards,
            *self.statuses_own_wards,
            self.values_auth.id(),
            *self.statuses_mono_auth_wards,
            self.tokens_auth.id(),
        )
    }

    #[logic(inline)]
    fn protocol(self) -> bool {
        pearlite! {
            let len = self.statuses_own.len();

            (len == self.cells_own.len()) &&
            (len == self.statuses_mono_auth.len()) &&

            (len == self.cells_wards.len()) &&
            (len == self.statuses_own_wards.len()) &&
            (len == self.statuses_mono_auth_wards.len()) &&

            (forall<i> 0 <= i && i < len ==>
                match self.cells_own[i] {
                    Some(at_view) => *at_view.val().ward() == self.cells_wards[i],
                    _ => true
                }) &&

            (forall<i> 0 <= i && i < len ==>
                *self.statuses_own[i].ward() == self.statuses_own_wards[i]) &&

            (forall<i> 0 <= i && i < len ==>
                self.statuses_mono_auth[i].id() == self.statuses_mono_auth_wards[i]) &&

            // 0 <= t <= h <= t + len
            (0 <= *self.tail && *self.tail <= *self.head && *self.head <= *self.tail + len) &&

            // head ~> (h, H)
            (forall<ts> #[trigger(self.head_own.val().get(ts))]
                self.head_own.val().contains(ts) ==>
                    self.head_own.val()[ts].0@ == *self.head ||
                    self.head_own.val().contains(ts + 1)
            ) &&

            // tail ~> (t, T)
            (forall<ts> #[trigger(self.tail_own.val().get(ts))]
                self.tail_own.val().contains(ts) ==>
                    self.tail_own.val()[ts].0@ == *self.tail ||
                    self.tail_own.val().contains(ts + 1)
            ) &&

            // statuses ~>* [(s_0, S_0), ..., (s_len - 1, S_len - 1)]
            // { i -> •(s_i, S_i) | 0 <= i < len }
            (forall<i: Int, ts: Int> #[trigger(self.statuses_own[i].val().get(ts))]
                 0 <= i && i < len ==>
                 match (self.statuses_own[i].val().get(ts)) {
                     Some((status, view)) => StatusWithView { status: status@, view } <= self.statuses_mono_auth[i].val(),
                     _ => true
                 }) &&

            // • [(v_t, V_t), ..., (v_h-1, V_h-1)]
            self.values_auth.val() == *self.values &&
            self.values.len() == *self.head - *self.tail &&

            // •({ k -> ()         | h <= k < t + len }
            //   { k -> (v_k, V_k) | t <= k < h       })

            // ∗{h - len <= k < t} s_k = 2k + 1 \/ Available k (s_k, S_k)
            (forall<k: Int> #[trigger(k.rem_euclid(len))] *self.head <= k && k < *self.tail + len ==>
             match self.statuses_mono_auth[k.rem_euclid(len)].val() {
                 StatusWithView { status, view } =>
                     (status == 2 * (k - len) + 1 &&
                      self.tokens_auth.val(k) == tokens::State::R) ||
                     (status == 2 * k &&
                      match self.cells_own[k.rem_euclid(len)] {
                          Some(at_view) => view >= at_view.view(),
                          _ => false
                      } &&
                      self.tokens_auth.val(k) == tokens::State::None)
             }) &&

            // ∗{t <= k < h} s_k = 2k \/ Occupied k (s_k, S_k) (v_k, V_k)
            (forall<k: Int> #[trigger(k.rem_euclid(len))] *self.tail <= k && k < *self.head ==>
             match self.statuses_mono_auth[k.rem_euclid(len)].val() {
                 StatusWithView { status, view } => {
                     let value = self.values[k - *self.tail];
                     (status == 2 * k &&
                      self.tokens_auth.val(k) == tokens::State::W(self.values[k - *self.tail])) ||
                     (status == 2 * k + 1 &&
                      match self.cells_own[k.rem_euclid(len)] {
                          Some(at_view) => view >= at_view.view() && at_view.val().val()@ == Some(value),
                          _ => false
                      } &&
                      self.tokens_auth.val(k) == tokens::State::None)
                 }
            })
        }
    }
}

pub struct Queue<T> {
    // cells: [QueueCell<T>; N],
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
            let (head, tail, cells_ward, statuses_ward, _, statuses_mono_auth_wards, _) = self.inv.public();
            let cells = self.cells@;
            let len = cells.len();

            0 < len &&
            head == self.head &&
            tail == self.tail &&
            cells_ward.len() == len &&
            statuses_ward.len() == len &&
            statuses_mono_auth_wards.len() == len &&

            (forall<i> 0 <= i && i < cells_ward.len() ==> cells_ward[i] == cells[i].item) &&
            (forall<i> 0 <= i && i < statuses_ward.len() ==> statuses_ward[i] == cells[i].status) &&

            self.inv.namespace() == BOUNDED_MPMC_QUEUE()
        }
    }
}

// impl<T> QueueCell<T> {
//     #[ensures(result.0.item == *result.1.ward())]
//     #[ensures(result.0.status == *result.2.ward())]
//     #[ensures(result.2.val().get(t).map_logic(|x: (usize, SyncView)| x.0) == Some(init))]
//     fn new(
//         init: usize,
//     ) -> (
//         QueueCell<T>,
//         Ghost<Perm<PermCell<MaybeUninit<T>>>>,
//         Ghost<Perm<AtomicUsize>>,
//     ) {
//         let view = SyncView::new()
//         let (status, status_own) = AtomicUsize::new(init, view.borrow_new());
//         let (item, item_own) = PermCell::new(MaybeUninit::uninit());

//         (QueueCell { item, status }, item_own, status_own)
//     }
// }

// // TODO: [VL] Backport to creusot-std
// #[requires(forall<fs: Seq<F>, rs: Seq<T>>
//     fs[0] == f && fs.len() == N@ + 1 && rs.len() == N@ &&
//     (forall<i> 0usize <= i && i < N ==>
//        fs[i@].postcondition_mut((i, Snapshot::new(rs[..i@])), fs[i@ + 1], rs[i@])) ==>
//     (forall<i> 0usize <= i && i < N ==>
//        fs[i@].postcondition_mut((i, Snapshot::new(rs[..i@])), fs[i@ + 1], rs[i@]) ==>
//        fs[i@ + 1].precondition((i + 1usize, Snapshot::new(rs[..i@ + 1])))) &&
//     fs[0].precondition((0usize, Snapshot::new(Seq::empty())))
// )]
// #[ensures(exists<fs: Seq<F>>
//     fs.len() == N@ + 1 &&
//     fs[0] == f &&
//     (forall<i> 0usize <= i && i < N ==>
//       exists<s: Seq<T>>
//         s.len() == i@ &&
//         (forall<j> 0 <= j && j < i@ ==> s[j] == result[j] && inv(s[j])) &&
//         fs[i@].postcondition_mut((i, Snapshot::new(s)), fs[i@ + 1], result[i@]))
// )]
// #[trusted]
// fn from_fn<T, const N: usize, F>(f: F) -> [T; N]
// where
//     F: FnMut(usize, Snapshot<Seq<T>>) -> T,
// {
//     panic!("Plop")
// }

impl<T> Queue<T> {
    // TODO: [VL] Pê longueur minimale == 2, voir paire
    #[requires(0 < 2 * length@ && 2 * length@ <= usize::MAX@)]
    #[ensures(result.0 == result.1.ward())]
    #[ensures(result.1@ == Seq::empty())]
    pub fn new(length: usize) -> (Self, Ghost<PermQueue<T>>) {
        let mut tokens_auth: Ghost<tokens::Authority<T>> = tokens::Authority::alloc();
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
        let (tail, tail_own) = AtomicUsize::new(0, SyncView::new().borrow_mut());

        let cells_wards = snapshot!(
            cells_own.map(|x: Option<AtView<PermPermCell<T>>>| *x.unwrap_logic().val().ward())
        );
        let statuses_own_wards = snapshot!(statuses_own.map(|x: Perm<AtomicUsize>| *x.ward()));
        let statuses_mono_auth_wards =
            snapshot!(statuses_mono_auth.map(|x: statuses::Authority| x.id()));

        let (values_auth, perm_queue) = values::Authority::alloc(snapshot!(Seq::empty()));

        let inv = AtomicInvariant::new(
            ghost!(QueueInv {
                head_own: head_own.into_inner(),
                tail_own: tail_own.into_inner(),
                cells_own: cells_own.into_inner(),
                statuses_own: statuses_own.into_inner(),

                values_auth: values_auth.into_inner(),
                statuses_mono_auth: statuses_mono_auth.into_inner(),
                tokens_auth: tokens_auth.into_inner(),

                head: snapshot!(0),
                tail: snapshot!(0),
                values: snapshot!(Seq::empty()),

                cells_wards,
                statuses_own_wards,
                statuses_mono_auth_wards,
            }),
            snapshot!(BOUNDED_MPMC_QUEUE()),
        );

        let queue = Queue {
            cells,
            head,
            tail,
            inv,
        };

        let perm_queue = ghost!(PermQueue {
            fragment: perm_queue.into_inner(),
            ward: snapshot!(queue)
        });

        (queue, perm_queue)
    }

    // TODO [VL]: Add a user committer at the serialisation point
    // It might only contains •([(v_t, V_t), ..., [(v_h-1, V_h-1)]])
    #[requires(tokens.contains(BOUNDED_MPMC_QUEUE()))]
    #[requires(*self == (*perm_queue).ward())]
    #[ensures(*self == (^perm_queue).ward())]
    #[ensures(result ==> (^perm_queue)@ == (*perm_queue)@.push_back(item))]
    #[ensures(!result ==> (^perm_queue)@ == (*perm_queue)@)]
    pub fn try_enqueue(
        &self,
        item: T,
        mut tokens: Ghost<Tokens>,
        mut perm_queue: Ghost<&mut PermQueue<T>>,
    ) -> bool {
        let mut view = SyncView::new();
        let mut witness: Ghost<Option<statuses::Fragment>> = ghost!(None);

        let head = self.head.load(ghost! { |c: &Committer<_, _, Relaxed, _>| {
            self.inv.open(tokens.reborrow(), |inv: &mut QueueInv<T>| {
                c.shoot_load(&inv.head_own, &mut SyncView::new());
            });
        } });

        let index = head % self.cells.len();
        let index_ghost: Ghost<Int> = snapshot!(index@).into_ghost();
        proof_assert!(*index_ghost == head@.rem_euclid(self.cells@.len()));

        let cell = &self.cells[index];
        let status = cell.status.load(ghost! { |c: &Committer<_, _, Acquire, _>| {
            self.inv.open(tokens.reborrow(), |inv: &mut QueueInv<T>| {
                c.shoot_load(&inv.statuses_own[*index_ghost], &mut view.borrow_mut());

                let status_view = snapshot!(StatusWithView { status: c.val_load()@, view: *view });
                proof_assert!(*status_view <= inv.statuses_mono_auth[*index_ghost].val()); // TODO: [VL] Try remove proof_assert!
                *witness = Some(inv.statuses_mono_auth[*index_ghost].get_fragment(status_view));
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
                    c.shoot_load(&inv.head_own, &mut view.borrow_mut());
                    c.shoot_store(&mut inv.head_own, &mut view.borrow_mut(), *ReleaseSyncView::new());

                    inv.statuses_mono_auth[*index_ghost].frag_lemma(witness.as_ref().unwrap());

                    let _ = snapshot!(rem_euclid_minus);
                    let toto = snapshot!((head@ - inv.cells_own.len()).rem_euclid(inv.cells_own.len()));
                    proof_assert!(*toto == *index_ghost);

                    proof_assert!(head@ < *inv.tail + inv.cells_own.len());
                    proof_assert!(inv.statuses_mono_auth[*index_ghost].val().status == 2 * head@);
                    *cell_own = Some(inv.cells_own[*index_ghost].take().unwrap().sync(*view));

                    let head_ghost = *snapshot!(head@).into_ghost();
                    *token = Some(tokens::TokenW::alloc(Ghost::new(&mut inv.tokens_auth), head_ghost, snapshot!(item)).into_inner());

                    let item_snap = snapshot!(item); // TODO: [VL] Do MWE, then bug report
                    inv.values_auth.update(&mut perm_queue.fragment, item_snap);
                    inv.values = snapshot!(inv.values.push_back(item));

                    inv.head = snapshot!(head@ + 1);
                });
            }}
        );

        if res.is_err() {
            return false;
        }

        unsafe {
            cell.item
                .set(ghost!(cell_own.as_mut().unwrap()), MaybeUninit::new(item))
        };

        cell.status.store(
            2 * head + 1,
            ghost! { |c: &mut Committer<_, _, _, Release>| {
                self.inv.open(tokens.reborrow(), |inv: &mut QueueInv<T>| {
                    let (mut view, at_view) = AtView::new(Ghost::new(cell_own.into_inner().unwrap())).into_inner();
                    c.shoot_store(&mut inv.statuses_own[*index_ghost], &mut view);

                    tokens::TokenW::discard(ghost!(token.into_inner().unwrap()), Ghost::new(&mut inv.tokens_auth));

                    let status_view = snapshot!(StatusWithView { status: c.val_store()@, view });
                    inv.statuses_mono_auth[*index_ghost].frag_lemma(witness.as_ref().unwrap());
                    inv.statuses_mono_auth[*index_ghost].increase(status_view);

                    inv.cells_own[*index_ghost] = Some(at_view);
                });
            }},
        );

        true
    }

    pub fn try_dequeue(&self) -> Option<T> {
        let tail = self
            .tail
            .load(ghost! { |c: &Committer<_, _, Relaxed, _>| {} });

        let cell = &self.cells[tail % self.cells.len()];
        let status = cell
            .status
            .load(ghost! { |c: &Committer<_, _, Acquire, _>| {} });

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
        cell.status.store(
            tail + self.cells.len(),
            ghost! { |c: &mut Committer<_, _, _, Release>| {} },
        );

        Some(item)
    }
}
