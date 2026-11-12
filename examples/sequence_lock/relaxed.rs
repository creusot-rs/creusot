// DEPTH 10

// Sequence lock protecting a pair of `u32`, in the relaxed memory model.
//
// Translated from the Verus version:
// <https://github.com/zero-to-nat/verus-relaxed-memory/blob/pldi2027-cleanup/wm-examples/src/seq_lock.rs>
// which is itself based on
// <https://jeehoonkang.github.io/2017/08/23/synchronization-patterns.html> and
// <https://github.com/Amanieu/seqlock/blob/master/src/lib.rs>.

use core::sync::atomic::Ordering;

use creusot_std::{
    ghost::{
        FnGhost,
        invariant::{AtomicInvariant, Protocol, Tokens, declare_namespace},
        perm::Perm,
        resource,
    },
    logic::{FMap, Id, Mapping, ra::agree::Ag},
    prelude::*,
    std::sync::{
        atomic::{
            AtomicU32, AtomicUsize, fence_acquire, fence_release,
            ordering::{Acquire, Relaxed, Release},
        },
        committer::Committer,
        view::{AcquireSyncView, ReleaseSyncView, SyncView, Timestamp},
    },
};

#[cfg(creusot)]
use creusot_std::std::sync::view::HasTimestamp;

declare_namespace! { SEQLOCK }

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

pub struct Write<T> {
    pub val: T,
    pub ts: Timestamp,
}

pub struct LockSnapshot {
    pub v0: u32,
    pub v1: u32,
    pub seq_ts: Timestamp,
    pub d0_ts: Timestamp,
    pub d1_ts: Timestamp,
}

impl LockSnapshot {
    #[logic(open)]
    pub fn value(self) -> (u32, u32) {
        (self.v0, self.v1)
    }
}

pub struct Latest {
    pub seq: Write<usize>,
    pub d0: Write<u32>,
    pub d1: Write<u32>,
    pub log: Seq<(u32, u32)>,
}

pub struct SeqLockLog(Fragment<Seq<(u32, u32)>>);

impl SeqLockLog {
    #[logic]
    pub fn id(self) -> Id {
        self.0.id()
    }
}

impl View for SeqLockLog {
    type ViewTy = Seq<(u32, u32)>;

    #[logic]
    fn view(self) -> Seq<(u32, u32)> {
        self.0.val()
    }
}

type Snapshots = FMap<Int, Ag<LockSnapshot>>;

/// Joins two witnesses of the acquire view of the current thread.
///
/// FIXME: this is missing from `creusot_std`. It is sound because both arguments are lower
/// bounds of the same thread-local acquire view, hence so is their join.
#[trusted]
#[check(ghost)]
#[ensures(result@ == a@.join(b@))]
fn acq_join(a: AcquireSyncView, b: AcquireSyncView) -> AcquireSyncView {
    let _ = b;
    a
}

struct SeqLockInv {
    seq_own: Perm<AtomicUsize>,
    data0_own: Perm<AtomicU32>,
    data1_own: Perm<AtomicU32>,

    latest: Authority<Latest>,
    latest_frag: Option<Fragment<Latest>>,

    log: Authority<Seq<(u32, u32)>>,
    snapshots: resource::Authority<Snapshots>,
    // The client's invariant on the values stored in the lock
    pred: Snapshot<Mapping<(u32, u32), bool>>,
}

impl SeqLockInv {
    #[logic]
    fn l(self) -> Latest {
        self.latest.val()
    }

    // The current sequence number
    #[logic]
    fn s(self) -> Int {
        pearlite! { self.l().seq.val@ }
    }

    #[logic]
    fn snap(self, n: Int) -> Option<LockSnapshot> {
        pearlite! {
            match self.snapshots@.lookup(n) {
                Some(Ag(sn)) => Some(sn),
                None => None,
            }
        }
    }

    #[logic(inline)]
    fn snapshot_inv(self, n: Int, sn: LockSnapshot) -> bool {
        pearlite! {
            (match self.seq_own.val().lookup(sn.seq_ts) {
                // A reader that loads `n` sees the snapshot's data writes
                Some((v, mv)) =>
                    v@ == n &&
                    self.data0_own.ward().get_timestamp(mv) >= sn.d0_ts &&
                    self.data1_own.ward().get_timestamp(mv) >= sn.d1_ts,
                None => false,
            }) &&
            (match self.data0_own.val().lookup(sn.d0_ts) { Some((v, _)) => v == sn.v0, None => false }) &&
            (match self.data1_own.val().lookup(sn.d1_ts) { Some((v, _)) => v == sn.v1, None => false })
        }
    }

    // The history of `seq`: each sequence number is written once, in increasing order,
    // and each even sequence number older than the latest one was immediately overwritten
    // by a writer's CAS.
    #[logic(inline)]
    fn seq_hist_inv(self) -> bool {
        pearlite! {
            (forall<ts> match self.seq_own.val().lookup(ts) {
                Some((v, _)) =>
                    v@ <= self.s() && ts <= self.l().seq.ts &&
                    (v@ % 2 == 0 && ts != self.l().seq.ts ==> self.seq_own.val().contains_logic(ts + 1)),
                None => true,
            }) &&
            (match self.seq_own.val().lookup(self.l().seq.ts) {
                Some((v, _)) => v == self.l().seq.val,
                None => false,
            }) &&
            (forall<t1, t2> match (self.seq_own.val().lookup(t1), self.seq_own.val().lookup(t2)) {
                (Some((v1, _)), Some((v2, _))) => t1 < t2 ==> v1@ < v2@,
                _ => true,
            })
        }
    }

    // The latest writes to `data0` and `data1`.
    #[logic(inline)]
    fn data_hist_inv(self) -> bool {
        pearlite! {
            (forall<ts> self.data0_own.val().contains_logic(ts) ==> ts <= self.l().d0.ts) &&
            (match self.data0_own.val().lookup(self.l().d0.ts) {
                Some((v, _)) => v == self.l().d0.val,
                None => false,
            }) &&
            (forall<ts> self.data1_own.val().contains_logic(ts) ==> ts <= self.l().d1.ts) &&
            (match self.data1_own.val().lookup(self.l().d1.ts) {
                Some((v, _)) => v == self.l().d1.val,
                None => false,
            })
        }
    }

    // If a data write is newer than a snapshot's data write, then its message view has a
    // newer timestamp for `seq` than the snapshot's write to `seq`.
    // A reader that reads such a data write will then see `seq` change.
    #[logic(inline)]
    fn data_sync_inv(self) -> bool {
        pearlite! {
            (forall<n, ts> match (self.snap(n), self.data0_own.val().lookup(ts)) {
                (Some(sn), Some((_, mv))) =>
                    ts > sn.d0_ts ==> self.seq_own.ward().get_timestamp(mv) > sn.seq_ts,
                _ => true,
            }) &&
            (forall<n, ts> match (self.snap(n), self.data1_own.val().lookup(ts)) {
                (Some(sn), Some((_, mv))) =>
                    ts > sn.d1_ts ==> self.seq_own.ward().get_timestamp(mv) > sn.seq_ts,
                _ => true,
            })
        }
    }

    #[logic(inline)]
    fn snapshots_inv(self) -> bool {
        pearlite! {
            // The snapshots are at even sequence numbers so far, and are in the histories
            (forall<n> match self.snap(n) {
                Some(sn) => n % 2 == 0 && 0 <= n && n <= self.s() && self.snapshot_inv(n, sn),
                None => true,
            }) &&
            // The i-th log entry is the snapshot at sequence number 2 * i
            (forall<i> 0 <= i && i < self.l().log.len() ==>
                match self.snap(2 * i) { Some(sn) => self.l().log[i] == sn.value(), None => false }) &&
            // While unlocked, the latest snapshot holds the latest writes
            (self.s() % 2 == 0 ==> self.snap(self.s()) == Some(LockSnapshot {
                v0: self.l().d0.val,
                v1: self.l().d1.val,
                seq_ts: self.l().seq.ts,
                d0_ts: self.l().d0.ts,
                d1_ts: self.l().d1.ts,
            }))
        }
    }
}

impl Protocol for SeqLockInv {
    type Public = (AtomicUsize, AtomicU32, AtomicU32, Id, Id, Id, Mapping<(u32, u32), bool>);

    #[logic]
    fn public(self) -> Self::Public {
        (
            *self.seq_own.ward(),
            *self.data0_own.ward(),
            *self.data1_own.ward(),
            self.latest.id(),
            self.log.id(),
            self.snapshots.id(),
            *self.pred,
        )
    }

    #[logic(inline)]
    fn protocol(self) -> bool {
        pearlite! {
            // The writer's half of `latest` is here iff the sequence number is even
            (match self.latest_frag {
                Some(f) => self.s() % 2 == 0 && f.id() == self.latest.id(),
                None => self.s() % 2 == 1,
            }) &&
            self.l().log == self.log.val() &&
            (if self.s() % 2 == 0 {
                self.s() == 2 * self.l().log.len() - 2
            } else {
                self.s() == 2 * self.l().log.len() - 1
            }) &&
            // Every value committed to the lock satisfies the client's invariant
            (forall<i> 0 <= i && i < self.l().log.len() ==> self.pred.get(self.l().log[i])) &&
            self.seq_hist_inv() &&
            self.data_hist_inv() &&
            self.snapshots_inv() &&
            self.data_sync_inv()
        }
    }
}

pub struct SeqLock {
    seq: AtomicUsize,
    data0: AtomicU32,
    data1: AtomicU32,
    inv: Ghost<AtomicInvariant<SeqLockInv>>,
}

impl Invariant for SeqLock {
    #[logic(inline)]
    fn invariant(self) -> bool {
        pearlite! {
            let (seq, data0, data1, _, _, _, _) = self.inv.public();
            seq == self.seq && data0 == self.data0 && data1 == self.data1 &&
            self.inv.namespace() == SEQLOCK()
        }
    }
}

pub struct SeqLockCommitter<'a> {
    auth: &'a mut Authority<Seq<(u32, u32)>>,
    id: Snapshot<Id>,
    old_log: Snapshot<Seq<(u32, u32)>>,
    new_log: Snapshot<Seq<(u32, u32)>>,
    shot: bool,
}

impl Invariant for SeqLockCommitter<'_> {
    #[logic(inline)]
    fn invariant(self) -> bool {
        self.auth.id() == *self.id
            && if self.shot {
                self.auth.val() == *self.new_log
            } else {
                self.auth.val() == *self.old_log
            }
    }
}

impl SeqLockCommitter<'_> {
    #[logic]
    pub fn id(self) -> Id {
        *self.id
    }

    #[logic]
    pub fn old_log(self) -> Seq<(u32, u32)> {
        *self.old_log
    }

    #[logic]
    pub fn new_log(self) -> Seq<(u32, u32)> {
        *self.new_log
    }

    #[logic]
    pub fn shot(self) -> bool {
        self.shot
    }

    #[requires(!self.shot())]
    #[requires(self.id() == log.id())]
    #[ensures((^self).shot())]
    #[ensures((*self).hist_inv(^self))]
    #[ensures(log@ == self.old_log())]
    #[ensures((^log)@ == self.new_log())]
    #[ensures((^log).id() == log.id())]
    #[check(ghost)]
    pub fn shoot(&mut self, log: &mut SeqLockLog) {
        self.auth.update(&mut log.0, self.new_log);
        self.shot = true;
    }

    #[logic(inline, prophetic)]
    pub fn hist_inv(self, other: Self) -> bool {
        pearlite! {
            self.id == other.id && ^self.auth == ^other.auth &&
            self.old_log == other.old_log && self.new_log == other.new_log
        }
    }
}

impl SeqLock {
    #[logic]
    pub fn id(self) -> Id {
        self.inv.public().4
    }

    #[logic]
    pub fn pred(self) -> Mapping<(u32, u32), bool> {
        self.inv.public().6
    }

    #[logic]
    fn latest_id(self) -> Id {
        self.inv.public().3
    }

    #[requires(pred.get((val0, val1)))]
    #[ensures(result.0.pred() == *pred)]
    #[ensures(result.1.id() == result.0.id())]
    #[ensures(result.1@ == Seq::singleton((val0, val1)))]
    pub fn new(
        val0: u32,
        val1: u32,
        pred: Snapshot<Mapping<(u32, u32), bool>>,
    ) -> (Self, Ghost<SeqLockLog>) {
        let mut view = ghost!(SyncView::new().into_inner());
        let (data0, data0_own) = AtomicU32::new(val0, view.borrow_mut());
        let d0_ts = snapshot!(data0.get_timestamp(*view));
        let (data1, data1_own) = AtomicU32::new(val1, view.borrow_mut());
        let d1_ts = snapshot!(data1.get_timestamp(*view));
        let (seq, seq_own) = AtomicUsize::new(0, view.borrow_mut());
        let seq_ts = snapshot!(seq.get_timestamp(*view));

        let log0 = snapshot!(Seq::singleton((val0, val1)));
        let (latest, latest_frag) = ghost!(
            Authority::alloc(snapshot!(Latest {
                seq: Write { val: 0usize, ts: *seq_ts },
                d0: Write { val: val0, ts: *d0_ts },
                d1: Write { val: val1, ts: *d1_ts },
                log: *log0,
            }))
            .into_inner()
        )
        .split();

        let (log, log_frag) = ghost!(Authority::alloc(log0).into_inner()).split();
        let mut snapshots = ghost!(resource::Authority::alloc().into_inner());

        ghost! {
            let snap0 = snapshot!(LockSnapshot {
                v0: val0, v1: val1, seq_ts: *seq_ts, d0_ts: *d0_ts, d1_ts: *d1_ts,
            });
            snapshots.add_fragment(snapshot!(FMap::singleton(0, Ag(*snap0))));
        };

        let inv = ghost!(
            AtomicInvariant::new(
                ghost!(SeqLockInv {
                    seq_own: seq_own.into_inner(),
                    data0_own: data0_own.into_inner(),
                    data1_own: data1_own.into_inner(),
                    latest: latest.into_inner(),
                    latest_frag: Some(latest_frag.into_inner()),
                    log: log.into_inner(),
                    snapshots: snapshots.into_inner(),
                    pred,
                }),
                snapshot!(SEQLOCK()),
            )
            .into_inner()
        );
        (SeqLock { seq, data0, data1, inv }, ghost!(SeqLockLog(log_frag.into_inner())))
    }

    // Under weak memory, the value read is some entry of the log,
    // but not necessarily the last one.
    #[requires(tokens.contains(SEQLOCK()))]
    #[requires(forall<c: &mut SeqLockCommitter>
        inv(c) ==> !c.shot() ==> c.id() == self.id() ==> c.new_log() == c.old_log() ==>
        f.precondition((c,)) && (f.postcondition_once((c,), ()) ==> (^c).shot() && (*c).hist_inv(^c))
    )]
    #[ensures(exists<c: &mut SeqLockCommitter>
        !c.shot() && c.id() == self.id() && c.new_log() == c.old_log() &&
        f.postcondition_once((c,), ()) && c.old_log().contains(result)
    )]
    #[ensures(self.pred().get(result))]
    pub fn read<F>(&self, mut tokens: Ghost<Tokens>, f: Ghost<F>) -> (u32, u32)
    where
        F: FnGhost + FnOnce(&mut SeqLockCommitter),
    {
        let mut view = ghost!(SyncView::new().into_inner());
        let f_snap = snapshot!(*f);
        let mut f = ghost!(Some(f.into_inner()));

        #[invariant(tokens.contains(SEQLOCK()))]
        #[invariant(*f == Some(*f_snap))]
        loop {
            // Load the first sequence number. The acquire ordering ensures that
            // this is done before reading the data.
            let mut snap_frag: Ghost<Option<resource::Fragment<Snapshots>>> = ghost!(None);

            let seq1 = self.seq.load(
                Ordering::Acquire,
                ghost! { |c: &Committer<AtomicUsize, usize, Acquire, ()>| {
                    self.inv.open(tokens.reborrow(), |inv: &mut SeqLockInv| {
                        c.shoot_load(&inv.seq_own, &mut view);
                        let v: Int = *snapshot!(c.val_load()@).into_ghost();
                        if v % 2int == 0int {
                            // Learn the snapshot at `seq1`, whose data writes are now in our view
                            proof_assert!(2 * (v / 2) == v && v / 2 < inv.l().log.len());
                            let sn = snapshot!(inv.snap(v).unwrap_logic());
                            proof_assert!(inv.snapshot_inv(v, *sn));
                            proof_assert!(c.timestamp() == sn.seq_ts);
                            let old_snaps = snapshot!(inv.snapshots@);
                            *snap_frag = Some(inv.snapshots.add_fragment(snapshot!(FMap::singleton(v, Ag(*sn)))));
                            proof_assert!(inv.snapshots@.lookup(v) == Some(Ag(*sn)));
                            proof_assert!(inv.snapshots@.ext_eq(*old_snaps));
                        }
                    })
                }}
            );

            // If the sequence number is odd then it means a writer is currently
            // modifying the value.
            if seq1 % 2 != 0 {
                continue;
            }

            let sn = snapshot!(snap_frag.unwrap_logic()@.lookup(seq1@).unwrap_logic().0);

            // The data may be concurrently modified by a writer,
            // so these loads may read values from a later critical section.
            // In that case, their message views contain a later write to `seq`.
            let mut acq0 = ghost!(AcquireSyncView::new().into_inner());
            let result0 = self.data0.load(
                Ordering::Relaxed,
                ghost! { |c: &Committer<AtomicU32, u32, Relaxed, ()>| {
                    self.inv.open(tokens.reborrow(), |inv: &mut SeqLockInv| {
                        *acq0 = c.shoot_load(&inv.data0_own, &mut view);
                        inv.snapshots.frag_lemma(snap_frag.as_ref().unwrap());
                        proof_assert!(inv.snap(seq1@) == Some(*sn));
                        proof_assert!(c.timestamp() > sn.d0_ts ==> self.seq.get_timestamp((*acq0)@) > sn.seq_ts);
                        proof_assert!(self.data1.get_timestamp(*view) >= sn.d1_ts);
                    })
                }},
            );

            let mut acq1 = ghost!(AcquireSyncView::new().into_inner());
            let result1 = self.data1.load(
                Ordering::Relaxed,
                ghost! { |c: &Committer<AtomicU32, u32, Relaxed, ()>| {
                    self.inv.open(tokens.reborrow(), |inv: &mut SeqLockInv| {
                        *acq1 = c.shoot_load(&inv.data1_own, &mut view);
                        inv.snapshots.frag_lemma(snap_frag.as_ref().unwrap());
                        proof_assert!(inv.snap(seq1@) == Some(*sn));
                        proof_assert!(c.timestamp() >= sn.d1_ts);
                        proof_assert!(c.val_load() == sn.v1 || self.seq.get_timestamp((*acq1)@) > sn.seq_ts);
                    })
                }}
            );

            // Make sure the seq2 read occurs after reading the data. What we
            // ideally want is a load(Release), but the Release ordering is not
            // available on loads.
            // The acquire view must contain the message views of both data loads,
            // so that a later write to either one forces `seq2 != seq1`.
            let fence_view = fence_acquire(Ordering::Acquire, ghost!(acq_join(*acq0, *acq1)));
            ghost! { view.join_in(*fence_view) };

            // If the sequence number is the same then the data wasn't modified
            // while we were reading it, and can be returned.
            let seq2 = self.seq.load(
                Ordering::Relaxed,
                ghost! { |c: &Committer<AtomicUsize, usize, Relaxed, ()>| {
                    self.inv.open(tokens.reborrow(), |inv: &mut SeqLockInv| {
                        let old_inv = snapshot!(*inv);
                        c.shoot_load(&inv.seq_own, &mut view);
                        if c.val_load() == seq1 {
                            // The write to `seq` that we read is the one at `sn.seq_ts`,
                            // so neither data load read from a later critical section
                            inv.snapshots.frag_lemma(snap_frag.as_ref().unwrap());
                            proof_assert!(c.timestamp() == sn.seq_ts);
                            proof_assert!(inv.log.val()[seq1@ / 2] == (result0, result1));
                            // Linearization point: the values of the snapshot are a log entry
                            let old_log = snapshot!(inv.log.val());
                            f.take().unwrap()(&mut SeqLockCommitter {
                                auth: &mut inv.log,
                                id: snapshot!(self.id()),
                                old_log,
                                new_log: old_log,
                                shot: false,
                            });
                            proof_assert!(forall<i> 0 <= i && i < old_inv.l().log.len() ==> old_inv.snap(2 * i) != None);
                        }
                    })
                }}
            );

            if seq1 == seq2 {
                return (result0, result1);
            }
        }
    }

    #[requires(tokens.contains(SEQLOCK()))]
    #[requires(forall<c: &mut SeqLockCommitter>
        inv(c) ==> !c.shot() ==> c.id() == self.id() ==> c.new_log() == c.old_log() ==>
        f.precondition((c,)) && (f.postcondition_once((c,), ()) ==> (^c).shot() && (*c).hist_inv(^c))
    )]
    #[ensures(exists<c: &mut SeqLockCommitter>
        !c.shot() && c.id() == self.id() && c.new_log() == c.old_log() &&
        f.postcondition_once((c,), ()) &&
        result.log_at_lock() == c.old_log() &&
        result.value() == c.old_log()[c.old_log().len() - 1]
    )]
    #[ensures(result.seqlock() == *self)]
    #[ensures(self.pred().get(result.value()))]
    pub fn lock_write<F>(&self, mut tokens: Ghost<Tokens>, f: Ghost<F>) -> SeqLockGuard<'_>
    where
        F: FnGhost + FnOnce(&mut SeqLockCommitter),
    {
        let mut view = ghost!(SyncView::new().into_inner());
        let f_snap = snapshot!(*f);
        let mut f = ghost!(Some(f.into_inner()));

        #[invariant(tokens.contains(SEQLOCK()))]
        #[invariant(*f == Some(*f_snap))]
        loop {
            let seq = self.seq.load(
                Ordering::Relaxed,
                ghost! { |c: &Committer<AtomicUsize, usize, Relaxed, ()>| {
                    self.inv.open(tokens.reborrow(), |inv: &mut SeqLockInv| {
                        c.shoot_load(&inv.seq_own, &mut view);
                    })
                }},
            );

            if seq % 2 != 0 {
                continue;
            }

            // Increment the sequence number. At this point, the number will be odd,
            // which will force readers to spin until we finish writing.
            let next_seq = seq + 1;
            let mut latest_frag: Ghost<Option<Fragment<Latest>>> = ghost!(None);

            let res = self.seq.compare_exchange::<_, Acquire, Relaxed>(
                seq,
                next_seq,
                Ordering::Acquire,
                Ordering::Relaxed,
                ghost! { |c: Result<&mut Committer<AtomicUsize, usize, Acquire, Relaxed>, &Committer<AtomicUsize, usize, Relaxed, ()>>| {
                    let Ok(c) = c else { return; };
                    self.inv.open(tokens.reborrow(), |inv: &mut SeqLockInv| {
                        c.shoot_load(&inv.seq_own, &mut view);
                        c.shoot_store(&mut inv.seq_own, &mut view, *ReleaseSyncView::new());
                        let mut fr = inv.latest_frag.take().unwrap();
                        let l = snapshot!(inv.l());
                        let new_l = snapshot!(Latest {
                            seq: Write { val: next_seq, ts: c.timestamp() + 1 },
                            d0: l.d0,
                            d1: l.d1,
                            log: l.log,
                        });
                        inv.latest.update(&mut fr, new_l);
                        // Linearization point: acquire the lock
                        let old_log = snapshot!(inv.log.val());
                        f.take().unwrap()(&mut SeqLockCommitter {
                            auth: &mut inv.log,
                            id: snapshot!(self.id()),
                            old_log,
                            new_log: old_log,
                            shot: false,
                        });
                        proof_assert!(self.pred().get((fr.val().d0.val, fr.val().d1.val)));
                        *latest_frag = Some(fr);
                    })
                }},
            );

            if res.is_err() {
                continue;
            }

            let rel = fence_release(Ordering::Release, view);

            return SeqLockGuard {
                seqlock: self,
                seq: next_seq,
                latest: ghost!(latest_frag.into_inner().unwrap()),
                view,
                rel,
            };
        }
    }

    #[requires(tokens.contains(SEQLOCK()))]
    #[requires(log.id() == self.id())]
    #[ensures(result == log@[log@.len() - 1])]
    #[ensures(self.pred().get(result))]
    pub fn into_inner(self, mut log: Ghost<SeqLockLog>, mut tokens: Ghost<Tokens>) -> (u32, u32) {
        let lock = self.lock_write(
            ghost!(tokens.reborrow()),
            ghost!(|c: &mut SeqLockCommitter| c.shoot(&mut log)),
        );

        lock.read(tokens)
    }
}

pub struct SeqLockGuard<'a> {
    seqlock: &'a SeqLock,
    seq: usize,

    // The writer's half of the latest writes
    latest: Ghost<Fragment<Latest>>,

    // The writer's view, threaded through the critical section
    view: Ghost<SyncView>,

    // The release view from the fence in `lock_write`, attached to the relaxed data stores
    rel: Ghost<ReleaseSyncView>,
}

impl Invariant for SeqLockGuard<'_> {
    #[logic(inline)]
    fn invariant(self) -> bool {
        pearlite! {
            self.latest.id() == self.seqlock.latest_id() &&
            self.latest.val().seq.val == self.seq &&
            self.seq@ % 2 == 1 &&
            self.seq@ == 2 * self.log_at_lock().len() - 1 &&
            // The writer's views contain the latest writes
            self.seqlock.seq.get_timestamp(*self.view) >= self.latest.val().seq.ts &&
            self.seqlock.seq.get_timestamp(self.rel@) >= self.latest.val().seq.ts &&
            self.seqlock.data0.get_timestamp(*self.view) >= self.latest.val().d0.ts &&
            self.seqlock.data1.get_timestamp(*self.view) >= self.latest.val().d1.ts
        }
    }
}

impl SeqLockGuard<'_> {
    #[logic]
    pub fn seqlock(self) -> SeqLock {
        *self.seqlock
    }

    #[logic]
    pub fn value(self) -> (u32, u32) {
        (self.latest.val().d0.val, self.latest.val().d1.val)
    }

    // The log at the time this guard acquired the lock.
    // No other writer can commit while the guard is held, so this is still the current log.
    #[logic]
    pub fn log_at_lock(self) -> Seq<(u32, u32)> {
        self.latest.val().log
    }

    #[requires(tokens.contains(SEQLOCK()))]
    #[ensures(result == self.value())]
    pub fn read(&self, mut tokens: Ghost<Tokens>) -> (u32, u32) {
        let mut view = ghost!(*self.view);

        let ret0 = self.seqlock.data0.load(
            Ordering::Relaxed,
            ghost! { |c: &Committer<AtomicU32, u32, Relaxed, ()>| {
                self.seqlock.inv.open(tokens.reborrow(), |inv: &mut SeqLockInv| {
                    // Only the writer writes `data0`, and its view contains its latest write,
                    // so the load reads that write
                    c.shoot_load(&inv.data0_own, &mut view);
                    inv.latest.agree(&self.latest);
                })
            }},
        );

        let ret1 = self.seqlock.data1.load(
            Ordering::Relaxed,
            ghost! { |c: &Committer<AtomicU32, u32, Relaxed, ()>| {
                self.seqlock.inv.open(tokens.reborrow(), |inv: &mut SeqLockInv| {
                    c.shoot_load(&inv.data1_own, &mut view);
                    inv.latest.agree(&self.latest);
                })
            }},
        );

        (ret0, ret1)
    }

    #[requires(tokens.contains(SEQLOCK()))]
    #[ensures((^self).seqlock() == (*self).seqlock())]
    #[ensures((^self).log_at_lock() == (*self).log_at_lock())]
    #[ensures((^self).value() == (val0, val1))]
    pub fn write(&mut self, val0: u32, val1: u32, mut tokens: Ghost<Tokens>) {
        self.seqlock.data0.store(
            val0,
            Ordering::Relaxed,
            ghost! { |c: &mut Committer<AtomicU32, u32, (), Relaxed>| {
                self.seqlock.inv.open(tokens.reborrow(), |inv: &mut SeqLockInv| {
                    inv.latest.agree(&self.latest);
                    c.shoot_store(&mut inv.data0_own, &mut self.view, *self.rel);
                    let l = snapshot!(inv.l());
                    let new_l = snapshot!(Latest {
                        seq: l.seq,
                        d0: Write { val: val0, ts: c.timestamp() + 1 },
                        d1: l.d1,
                        log: l.log,
                    });
                    inv.latest.update(&mut self.latest, new_l);
                })
            }},
        );
        self.seqlock.data1.store(
            val1,
            Ordering::Relaxed,
            ghost! { |c: &mut Committer<AtomicU32, u32, (), Relaxed>| {
                self.seqlock.inv.open(tokens.reborrow(), |inv: &mut SeqLockInv| {
                    inv.latest.agree(&self.latest);
                    c.shoot_store(&mut inv.data1_own, &mut self.view, *self.rel);
                    let l = snapshot!(inv.l());
                    let new_l = snapshot!(Latest {
                        seq: l.seq,
                        d0: l.d0,
                        d1: Write { val: val1, ts: c.timestamp() + 1 },
                        log: l.log,
                    });
                    inv.latest.update(&mut self.latest, new_l);
                })
            }},
        );
    }

    #[requires(tokens.contains(SEQLOCK()))]
    #[requires(self.seqlock().pred().get(self.value()))]
    #[requires(2 * self.log_at_lock().len() <= usize::MAX@)]
    #[requires(forall<c: &mut SeqLockCommitter>
        inv(c) ==> !c.shot() ==> c.id() == self.seqlock().id() ==>
        c.old_log() == self.log_at_lock() ==> c.new_log() == c.old_log().snoc(self.value()) ==>
        f.precondition((c,)) && (f.postcondition_once((c,), ()) ==> (^c).shot() && (*c).hist_inv(^c))
    )]
    #[ensures(exists<c: &mut SeqLockCommitter>
        !c.shot() && c.id() == self.seqlock().id() &&
        c.old_log() == self.log_at_lock() && c.new_log() == c.old_log().snoc(self.value()) &&
        f.postcondition_once((c,), ())
    )]
    pub fn unlock<F>(self, mut tokens: Ghost<Tokens>, f: Ghost<F>)
    where
        F: FnGhost + FnOnce(&mut SeqLockCommitter),
    {
        // Increment the sequence number again, which will make it even and
        // allow readers to access the data. The release ordering ensures that
        // all writes to the data are done before writing the sequence number.
        let next_seq = self.seq + 1;
        let SeqLockGuard { seqlock, mut latest, mut view, .. } = self;

        seqlock.seq.store(
            next_seq,
            Ordering::Release,
            ghost! { |c: &mut Committer<AtomicUsize, usize, (), Release>| {
                seqlock.inv.open(tokens.reborrow(), |inv: &mut SeqLockInv| {
                    inv.latest.agree(&latest);
                    c.shoot_store(&mut inv.seq_own, &mut view);
                    let l = snapshot!(inv.l());
                    let new_snap = snapshot!(LockSnapshot {
                        v0: l.d0.val,
                        v1: l.d1.val,
                        seq_ts: c.timestamp() + 1,
                        d0_ts: l.d0.ts,
                        d1_ts: l.d1.ts,
                    });
                    inv.snapshots.add_fragment(snapshot!(FMap::singleton(next_seq@, Ag(*new_snap))));
                    let old_log = snapshot!(l.log);
                    let new_log = snapshot!(old_log.snoc((l.d0.val, l.d1.val)));
                    let new_l = snapshot!(Latest {
                        seq: Write { val: next_seq, ts: c.timestamp() + 1 },
                        d0: l.d0,
                        d1: l.d1,
                        log: *new_log,
                    });
                    inv.latest.update(&mut latest, new_l);
                    // Linearization point: append the guard's value to the log
                    f.into_inner()(&mut SeqLockCommitter {
                        auth: &mut inv.log,
                        id: snapshot!(seqlock.id()),
                        old_log,
                        new_log,
                        shot: false,
                    });
                    inv.latest_frag = Some(latest.into_inner());
                })
            }},
        );
    }
}
