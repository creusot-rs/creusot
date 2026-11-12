//! Sequence lock protecting a pair of `u32`, in the sequentially consistent memory model.
//!
//! Translated from the Verus version:
//! <https://github.com/zero-to-nat/verus-relaxed-memory/blob/pldi2027-cleanup/wm-examples/src/seq_lock.rs>
//! which is itself based on
//! <https://jeehoonkang.github.io/2017/08/23/synchronization-patterns.html> and
//! <https://github.com/Amanieu/seqlock/blob/master/src/lib.rs>.
//!
//! The ghost state is described with resources:
//! - `latest`, a ghost variable holding the current values of `seq`, `data0` and `data1`
//!   and the log. One half is held by the invariant, and the other half is held by the
//!   invariant while the lock is free, and by the `SeqLockGuard` while it is held.
//! - `log`, a ghost variable holding the log of the values committed to the lock, the
//!   other half of which is held by the client (`SeqLockLog`).
//! - `snapshots`, a monotone map from every sequence number reached so far to the values
//!   of the data at that time (only meaningful for even sequence numbers). Its fragments
//!   are persistent knowledge for readers: they give the value committed at an even
//!   sequence number, and a lower bound on the current sequence number.

use core::sync::atomic::Ordering;

use creusot_std::{
    ghost::{
        FnGhost,
        invariant::{AtomicInvariantSC, Protocol, Tokens, declare_namespace},
        perm::Perm,
        resource,
    },
    logic::{FMap, Id, Mapping, ra::agree::Ag},
    prelude::*,
    std::sync::{
        atomic_sc::{AtomicU32, AtomicUsize, ordering::SeqCst},
        committer::Committer,
    },
};

declare_namespace! { SEQLOCK }

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

/// The current values of the atomics, and the log of the values committed to the lock.
pub struct Latest {
    pub seq: usize,
    pub d0: u32,
    pub d1: u32,
    pub log: Seq<(u32, u32)>,
}

/// Ghost token for the logical state of a `SeqLock`, owned by the client:
/// every value committed to the lock, oldest first.
/// The client holds this half of the ghost variable, and the lock's invariant holds the other half.
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

type Snapshots = FMap<Int, Ag<(u32, u32)>>;

struct SeqLockInv {
    seq_own: Perm<AtomicUsize>,
    data0_own: Perm<AtomicU32>,
    data1_own: Perm<AtomicU32>,
    latest: Authority<Latest>,
    /// The other half of `latest`, held here iff the lock is free.
    latest_frag: Option<Fragment<Latest>>,
    log: Authority<Seq<(u32, u32)>>,
    snapshots: resource::Authority<Snapshots>,
    /// The client's invariant on the values stored in the lock
    pred: Snapshot<Mapping<(u32, u32), bool>>,
}

impl SeqLockInv {
    #[logic]
    fn l(self) -> Latest {
        self.latest.val()
    }

    /// The current sequence number
    #[logic]
    fn s(self) -> Int {
        pearlite! { self.l().seq@ }
    }

    #[logic]
    fn snap(self, n: Int) -> Option<(u32, u32)> {
        pearlite! {
            match self.snapshots@.lookup(n) {
                Some(Ag(v)) => Some(v),
                None => None,
            }
        }
    }
}

impl Protocol for SeqLockInv {
    /// (seq, data0, data1, latest id, log id, snapshots id, pred)
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
            // The atomics hold the latest values
            self.seq_own.val() == self.l().seq &&
            self.data0_own.val() == self.l().d0 &&
            self.data1_own.val() == self.l().d1 &&
            // There is a snapshot for every sequence number reached so far
            (forall<n> (self.snap(n) != None) == (0 <= n && n <= self.s())) &&
            // The i-th log entry is the snapshot at sequence number 2 * i
            (forall<i> 0 <= i && i < self.l().log.len() ==> self.snap(2 * i) == Some(self.l().log[i])) &&
            // While unlocked, the latest snapshot holds the current data
            (self.s() % 2 == 0 ==> self.snap(self.s()) == Some((self.l().d0, self.l().d1)))
        }
    }
}

/// A sequential lock
pub struct SeqLock {
    seq: AtomicUsize,
    data0: AtomicU32,
    data1: AtomicU32,
    inv: Ghost<AtomicInvariantSC<SeqLockInv>>,
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

/// A logically atomic update of the log of the lock.
///
/// This is given to the client at the linearization points of `read`, `lock_write` and
/// `unlock`, which is required to "shoot" it, updating its own half of the log.
pub struct LogCommitter<'a> {
    auth: &'a mut Authority<Seq<(u32, u32)>>,
    id: Snapshot<Id>,
    old_log: Snapshot<Seq<(u32, u32)>>,
    new_log: Snapshot<Seq<(u32, u32)>>,
    shot: bool,
}

impl Invariant for LogCommitter<'_> {
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

impl LogCommitter<'_> {
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
    /// The ID of this lock, which its [`SeqLockLog`] token must match.
    #[logic]
    pub fn id(self) -> Id {
        self.inv.public().4
    }

    /// The client's invariant on the values stored in this lock.
    #[logic]
    pub fn pred(self) -> Mapping<(u32, u32), bool> {
        self.inv.public().6
    }

    #[logic]
    fn latest_id(self) -> Id {
        self.inv.public().3
    }

    /// Creates a new SeqLock with the given initial value, along with the token
    /// for its logical state.
    #[requires(pred.get((val0, val1)))]
    #[ensures(result.0.pred() == *pred)]
    #[ensures(result.1.id() == result.0.id())]
    #[ensures(result.1@ == Seq::singleton((val0, val1)))]
    pub fn new(
        val0: u32,
        val1: u32,
        pred: Snapshot<Mapping<(u32, u32), bool>>,
    ) -> (Self, Ghost<SeqLockLog>) {
        let (data0, data0_own) = AtomicU32::new(val0);
        let (data1, data1_own) = AtomicU32::new(val1);
        let (seq, seq_own) = AtomicUsize::new(0);

        let log0 = snapshot!(Seq::singleton((val0, val1)));
        let (latest, latest_frag) =
            Authority::alloc(snapshot!(Latest { seq: 0usize, d0: val0, d1: val1, log: *log0 }))
                .split();
        let (log, log_frag) = Authority::alloc(log0).split();
        let mut snapshots = resource::Authority::alloc();
        ghost! {
            snapshots.add_fragment(snapshot!(FMap::singleton(0, Ag((val0, val1)))));
        };

        let inv = AtomicInvariantSC::new(
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
        );
        (SeqLock { seq, data0, data1, inv }, ghost!(SeqLockLog(log_frag.into_inner())))
    }

    /// Reads the value protected by the `SeqLock`.
    ///
    /// This operation is extremely fast since it only reads the `SeqLock`,
    /// which allows multiple readers to read the value without interfering with
    /// each other.
    ///
    /// If a writer is currently modifying the contained value then the calling
    /// thread will block until the writer thread releases the lock.
    #[requires(tokens.contains(SEQLOCK()))]
    #[requires(forall<c: &mut LogCommitter>
        inv(c) ==> !c.shot() ==> c.id() == self.id() ==> c.new_log() == c.old_log() ==>
        f.precondition((c,)) && (f.postcondition_once((c,), ()) ==> (^c).shot() && (*c).hist_inv(^c))
    )]
    #[ensures(exists<c: &mut LogCommitter>
        !c.shot() && c.id() == self.id() && c.new_log() == c.old_log() &&
        f.postcondition_once((c,), ()) && c.old_log().contains(result)
    )]
    #[ensures(self.pred().get(result))]
    pub fn read<F>(&self, mut tokens: Ghost<Tokens>, f: Ghost<F>) -> (u32, u32)
    where
        F: FnGhost + FnOnce(&mut LogCommitter),
    {
        let f_snap = snapshot!(*f);
        let mut f = ghost!(Some(f.into_inner()));

        #[invariant(tokens.contains(SEQLOCK()))]
        #[invariant(*f == Some(*f_snap))]
        loop {
            // Load the first sequence number, and learn the snapshot at `seq1`.
            let mut snap_frag: Ghost<Option<resource::Fragment<Snapshots>>> = ghost!(None);
            let seq1 = self.seq.load(
                Ordering::SeqCst,
                ghost! { |c: &Committer<AtomicUsize, usize, SeqCst, ()>| {
                    self.inv.open(tokens.reborrow(), |inv: &mut SeqLockInv| {
                        c.shoot_load(&inv.seq_own);
                        let s = snapshot!(inv.s());
                        let sn = snapshot!(inv.snap(*s).unwrap_logic());
                        *snap_frag = Some(inv.snapshots.add_fragment(snapshot!(FMap::singleton(*s, Ag(*sn)))));
                    })
                }}
            );

            // If the sequence number is odd then it means a writer is currently
            // modifying the value.
            if seq1 % 2 != 0 {
                continue;
            }
            // The data may be concurrently modified by a writer.
            // We record the sequence number at the time of each data load
            // (as a fragment of `snapshots`, which is a lower bound for later sequence numbers).
            let mut lb0: Ghost<Option<resource::Fragment<Snapshots>>> = ghost!(None);
            let result0 = self.data0.load(
                Ordering::SeqCst,
                ghost! { |c: &Committer<AtomicU32, u32, SeqCst, ()>| {
                    self.inv.open(tokens.reborrow(), |inv: &mut SeqLockInv| {
                        c.shoot_load(&inv.data0_own);
                        inv.snapshots.frag_lemma(snap_frag.as_ref().unwrap());
                        let s = snapshot!(inv.s());
                        let v = snapshot!(inv.snap(*s).unwrap_logic());
                        *lb0 = Some(inv.snapshots.add_fragment(snapshot!(FMap::singleton(*s, Ag(*v)))));
                    })
                }},
            );

            let mut lb1: Ghost<Option<resource::Fragment<Snapshots>>> = ghost!(None);
            let result1 = self.data1.load(
                Ordering::SeqCst,
                ghost! { |c: &Committer<AtomicU32, u32, SeqCst, ()>| {
                    self.inv.open(tokens.reborrow(), |inv: &mut SeqLockInv| {
                        c.shoot_load(&inv.data1_own);
                        inv.snapshots.frag_lemma(lb0.as_ref().unwrap());
                        let s = snapshot!(inv.s());
                        let v = snapshot!(inv.snap(*s).unwrap_logic());
                        *lb1 = Some(inv.snapshots.add_fragment(snapshot!(FMap::singleton(*s, Ag(*v)))));
                    })
                }}
            );

            // If the sequence number is the same then the data wasn't modified
            // while we were reading it, and can be returned.
            let seq2 = self.seq.load(
                Ordering::SeqCst,
                ghost! { |c: &Committer<AtomicUsize, usize, SeqCst, ()>| {
                    self.inv.open(tokens.reborrow(), |inv: &mut SeqLockInv| {
                        c.shoot_load(&inv.seq_own);
                        inv.snapshots.frag_lemma(lb1.as_ref().unwrap());
                        if c.val_load() == seq1 {
                            proof_assert!(inv.log.val()[seq1@ / 2] == (result0, result1));
                            // Linearization point: the values of the snapshot are a log entry
                            let old_log = snapshot!(inv.log.val());
                            f.take().unwrap()(&mut LogCommitter {
                                auth: &mut inv.log,
                                id: snapshot!(self.id()),
                                old_log,
                                new_log: old_log,
                                shot: false,
                            });
                        }
                    })
                }},
            );

            if seq1 == seq2 {
                return (result0, result1);
            }
        }
    }

    /// Locks this `SeqLock` with exclusive write access, blocking the current
    /// thread until it can be acquired.
    ///
    /// This function does not block while waiting for concurrent readers.
    /// Instead, readers will detect the concurrent write and retry the read.
    /// (The Verus version splits this into `begin_write` and `lock_write`.)
    #[requires(tokens.contains(SEQLOCK()))]
    #[requires(forall<c: &mut LogCommitter>
        inv(c) ==> !c.shot() ==> c.id() == self.id() ==> c.new_log() == c.old_log() ==>
        f.precondition((c,)) && (f.postcondition_once((c,), ()) ==> (^c).shot() && (*c).hist_inv(^c))
    )]
    #[ensures(exists<c: &mut LogCommitter>
        !c.shot() && c.id() == self.id() && c.new_log() == c.old_log() &&
        f.postcondition_once((c,), ()) &&
        result.log_at_lock() == c.old_log() &&
        result.value() == c.old_log()[c.old_log().len() - 1]
    )]
    #[ensures(result.seqlock() == *self)]
    #[ensures(self.pred().get(result.value()))]
    pub fn lock_write<F>(&self, mut tokens: Ghost<Tokens>, f: Ghost<F>) -> SeqLockGuard<'_>
    where
        F: FnGhost + FnOnce(&mut LogCommitter),
    {
        let f_snap = snapshot!(*f);
        let mut f = ghost!(Some(f.into_inner()));

        #[invariant(tokens.contains(SEQLOCK()))]
        #[invariant(*f == Some(*f_snap))]
        loop {
            let seq = self.seq.load(
                Ordering::SeqCst,
                ghost! { |c: &Committer<AtomicUsize, usize, SeqCst, ()>| {
                    self.inv.open(tokens.reborrow(), |inv: &mut SeqLockInv| {
                        c.shoot_load(&inv.seq_own);
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
            let res = self.seq.compare_exchange(
                seq,
                next_seq,
                Ordering::SeqCst,
                Ordering::SeqCst,
                ghost! { |c: Result<&mut Committer<AtomicUsize, usize, SeqCst, SeqCst>, &Committer<AtomicUsize, usize, SeqCst, ()>>| {
                    let Ok(c) = c else { return; };
                    self.inv.open(tokens.reborrow(), |inv: &mut SeqLockInv| {
                        c.shoot_load(&inv.seq_own);
                        c.shoot_store(&mut inv.seq_own);
                        let mut fr = inv.latest_frag.take().unwrap();
                        let l = snapshot!(inv.l());
                        let new_l = snapshot!(Latest { seq: next_seq, d0: l.d0, d1: l.d1, log: l.log });
                        inv.latest.update(&mut fr, new_l);
                        inv.snapshots.add_fragment(snapshot!(FMap::singleton(next_seq@, Ag((l.d0, l.d1)))));
                        // Linearization point: acquire the lock
                        let old_log = snapshot!(inv.log.val());
                        f.take().unwrap()(&mut LogCommitter {
                            auth: &mut inv.log,
                            id: snapshot!(self.id()),
                            old_log,
                            new_log: old_log,
                            shot: false,
                        });
                        proof_assert!(self.pred().get((fr.val().d0, fr.val().d1)));
                        *latest_frag = Some(fr);
                    })
                }},
            );
            if res.is_err() {
                continue;
            }

            return SeqLockGuard {
                seqlock: self,
                seq: next_seq,
                latest: ghost!(latest_frag.into_inner().unwrap()),
            };
        }
    }

    /// Consumes this `SeqLock`, returning the underlying data.
    #[requires(tokens.contains(SEQLOCK()))]
    #[requires(log.id() == self.id())]
    #[ensures(result == log@[log@.len() - 1])]
    #[ensures(self.pred().get(result))]
    pub fn into_inner(self, mut log: Ghost<SeqLockLog>, mut tokens: Ghost<Tokens>) -> (u32, u32) {
        let lock = self.lock_write(
            ghost!(tokens.reborrow()),
            ghost!(|c: &mut LogCommitter| c.shoot(&mut log)),
        );
        lock.read(tokens)
    }
}

/// RAII structure used to release the exclusive write access of a `SeqLock`
/// when dropped.
pub struct SeqLockGuard<'a> {
    seqlock: &'a SeqLock,
    seq: usize,
    /// The writer's half of the latest values
    latest: Ghost<Fragment<Latest>>,
}

impl Invariant for SeqLockGuard<'_> {
    #[logic(inline)]
    fn invariant(self) -> bool {
        pearlite! {
            self.latest.id() == self.seqlock.latest_id() &&
            self.latest.val().seq == self.seq &&
            self.seq@ % 2 == 1 &&
            self.seq@ == 2 * self.log_at_lock().len() - 1
        }
    }
}

impl SeqLockGuard<'_> {
    /// The lock this guard belongs to.
    #[logic]
    pub fn seqlock(self) -> SeqLock {
        *self.seqlock
    }

    /// The value currently written by this guard.
    #[logic]
    pub fn value(self) -> (u32, u32) {
        (self.latest.val().d0, self.latest.val().d1)
    }

    /// The log at the time this guard acquired the lock.
    /// No other writer can commit while the guard is held, so this is still the current log.
    #[logic]
    pub fn log_at_lock(self) -> Seq<(u32, u32)> {
        self.latest.val().log
    }

    /// Reads the data in the `SeqLockGuard`
    /// (workaround for implementing `Deref`).
    #[requires(tokens.contains(SEQLOCK()))]
    #[ensures(result == self.value())]
    pub fn read(&self, mut tokens: Ghost<Tokens>) -> (u32, u32) {
        let ret0 = self.seqlock.data0.load(
            Ordering::SeqCst,
            ghost! { |c: &Committer<AtomicU32, u32, SeqCst, ()>| {
                self.seqlock.inv.open(tokens.reborrow(), |inv: &mut SeqLockInv| {
                    // Only the writer writes `data0`, so the load reads its latest write
                    c.shoot_load(&inv.data0_own);
                    inv.latest.agree(&self.latest);
                })
            }},
        );

        let ret1 = self.seqlock.data1.load(
            Ordering::SeqCst,
            ghost! { |c: &Committer<AtomicU32, u32, SeqCst, ()>| {
                self.seqlock.inv.open(tokens.reborrow(), |inv: &mut SeqLockInv| {
                    c.shoot_load(&inv.data1_own);
                    inv.latest.agree(&self.latest);
                })
            }},
        );

        (ret0, ret1)
    }

    /// Writes to the data in the `SeqLockGuard`.
    /// (Since this is a workaround for getting a mutable reference to the underlying data,
    /// we impose no restrictions on the values that are written at this time.)
    #[requires(tokens.contains(SEQLOCK()))]
    #[ensures((^self).seqlock() == (*self).seqlock())]
    #[ensures((^self).log_at_lock() == (*self).log_at_lock())]
    #[ensures((^self).value() == (val0, val1))]
    pub fn write(&mut self, val0: u32, val1: u32, mut tokens: Ghost<Tokens>) {
        self.seqlock.data0.store(
            val0,
            Ordering::SeqCst,
            ghost! { |c: &mut Committer<AtomicU32, u32, (), SeqCst>| {
                self.seqlock.inv.open(tokens.reborrow(), |inv: &mut SeqLockInv| {
                    inv.latest.agree(&self.latest);
                    c.shoot_store(&mut inv.data0_own);
                    let l = snapshot!(inv.l());
                    let new_l = snapshot!(Latest { seq: l.seq, d0: val0, d1: l.d1, log: l.log });
                    inv.latest.update(&mut self.latest, new_l);
                })
            }},
        );
        self.seqlock.data1.store(
            val1,
            Ordering::SeqCst,
            ghost! { |c: &mut Committer<AtomicU32, u32, (), SeqCst>| {
                self.seqlock.inv.open(tokens.reborrow(), |inv: &mut SeqLockInv| {
                    inv.latest.agree(&self.latest);
                    c.shoot_store(&mut inv.data1_own);
                    let l = snapshot!(inv.l());
                    let new_l = snapshot!(Latest { seq: l.seq, d0: l.d0, d1: val1, log: l.log });
                    inv.latest.update(&mut self.latest, new_l);
                })
            }},
        );
    }

    /// Releases the lock, committing the guard's value to the log.
    /// (Workaround for implementing `Drop`.)
    ///
    /// While a `SeqLockGuard` exists, the sequence number `s` is odd and
    /// `s == 2 * len - 1`, where `len == self.log_at_lock().len()`.
    /// Unlocking increments `s`, so requiring `2 * len <= usize::MAX` ensures
    /// `s + 1 <= usize::MAX`.
    #[requires(tokens.contains(SEQLOCK()))]
    #[requires(self.seqlock().pred().get(self.value()))]
    #[requires(2 * self.log_at_lock().len() <= usize::MAX@)]
    #[requires(forall<c: &mut LogCommitter>
        inv(c) ==> !c.shot() ==> c.id() == self.seqlock().id() ==>
        c.old_log() == self.log_at_lock() ==> c.new_log() == c.old_log().snoc(self.value()) ==>
        f.precondition((c,)) && (f.postcondition_once((c,), ()) ==> (^c).shot() && (*c).hist_inv(^c))
    )]
    #[ensures(exists<c: &mut LogCommitter>
        !c.shot() && c.id() == self.seqlock().id() &&
        c.old_log() == self.log_at_lock() && c.new_log() == c.old_log().snoc(self.value()) &&
        f.postcondition_once((c,), ())
    )]
    pub fn unlock<F>(self, mut tokens: Ghost<Tokens>, f: Ghost<F>)
    where
        F: FnGhost + FnOnce(&mut LogCommitter),
    {
        // Increment the sequence number again, which will make it even and
        // allow readers to access the data.
        let next_seq = self.seq + 1;
        let SeqLockGuard { seqlock, mut latest, .. } = self;
        seqlock.seq.store(
            next_seq,
            Ordering::SeqCst,
            ghost! { |c: &mut Committer<AtomicUsize, usize, (), SeqCst>| {
                seqlock.inv.open(tokens.reborrow(), |inv: &mut SeqLockInv| {
                    inv.latest.agree(&latest);
                    c.shoot_store(&mut inv.seq_own);
                    let l = snapshot!(inv.l());
                    inv.snapshots.add_fragment(snapshot!(FMap::singleton(next_seq@, Ag((l.d0, l.d1)))));
                    let old_log = snapshot!(l.log);
                    let new_log = snapshot!(old_log.snoc((l.d0, l.d1)));
                    let new_l = snapshot!(Latest { seq: next_seq, d0: l.d0, d1: l.d1, log: *new_log });
                    inv.latest.update(&mut latest, new_l);
                    // Linearization point: append the guard's value to the log
                    f.into_inner()(&mut LogCommitter {
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
