use std::rc::Rc;

use crate::analysis::{FrozenPlaces, MaybeLiveExceptDrop, MaybeUninitializedLocals};
use rustc_borrowck::{borrow_set::BorrowSet, consumers::RegionInferenceContext};
use rustc_index::bit_set::BitSet;
use rustc_middle::{
    mir::{traversal, BasicBlock, Body, Local, Location},
    ty::TyCtxt,
};
use rustc_mir_dataflow::{Analysis, ResultsCursor};

use crate::extended_location::ExtendedLocation;

pub struct EagerResolver<'body, 'tcx> {
    local_live: ResultsCursor<'body, 'tcx, MaybeLiveExceptDrop>,

    local_uninit: ResultsCursor<'body, 'tcx, MaybeUninitializedLocals>,

    frozen_places: ResultsCursor<'body, 'tcx, FrozenPlaces<'body, 'tcx>>,

    borrow_set: Rc<BorrowSet<'tcx>>,

    body: &'body Body<'tcx>,
}

impl<'body, 'tcx> EagerResolver<'body, 'tcx> {
    pub(crate) fn new(
        tcx: TyCtxt<'tcx>,
        body: &'body Body<'tcx>,
        borrow_set: Rc<BorrowSet<'tcx>>,
        regioncx: Rc<RegionInferenceContext<'tcx>>,
    ) -> Self {
        let local_uninit = MaybeUninitializedLocals
            .into_engine(tcx, body)
            .iterate_to_fixpoint()
            .into_results_cursor(body);

        // MaybeLiveExceptDrop ignores `drop` for the purpose of resolve liveness... unclear that this can
        // be sound.
        let local_live = MaybeLiveExceptDrop
            .into_engine(tcx, body)
            .iterate_to_fixpoint()
            .into_results_cursor(body);

        let frozen_places = FrozenPlaces::new(tcx, body, &regioncx, borrow_set.clone())
            .into_engine(tcx, body)
            .iterate_to_fixpoint()
            .into_results_cursor(body);

        EagerResolver { local_live, local_uninit, frozen_places, borrow_set, body }
    }

    fn seek_to(&mut self, loc: ExtendedLocation) {
        loc.seek_to(&mut self.local_live);
        loc.seek_to(&mut self.local_uninit);
        loc.seek_to(&mut self.frozen_places);
    }

    fn def_init_locals(&self) -> BitSet<Local> {
        let mut uninit: BitSet<_> = BitSet::new_empty(self.body.local_decls.len());
        uninit.union(self.local_uninit.get());

        let mut def_init = BitSet::new_filled(self.body.local_decls.len());
        def_init.subtract(&uninit);
        def_init
    }

    fn live_locals(&self) -> BitSet<Local> {
        let mut live: BitSet<_> = BitSet::new_empty(self.body.local_decls.len());
        live.union(self.local_live.get());
        live
    }

    fn frozen_locals(&self) -> BitSet<Local> {
        let mut frozen: BitSet<_> = BitSet::new_empty(self.body.local_decls.len());
        for bi in self.frozen_places.get().iter() {
            let l = self.borrow_set[bi].borrowed_place.local;
            frozen.insert(l);
        }
        frozen
    }

    /// Locals that need to be resolved eventually
    /// = (live ∪ frozen) ∩ initialized
    fn need_resolve_locals(&self) -> BitSet<Local> {
        let mut should_resolve = self.live_locals();
        should_resolve.union(&self.frozen_locals());
        should_resolve.intersect(&self.def_init_locals());
        should_resolve
    }

    /// Locals that have already been resolved
    /// = not live ∩ not frozen ∩ initialized
    fn resolved_locals(&self) -> BitSet<Local> {
        let mut resolved = self.def_init_locals();
        resolved.subtract(&self.frozen_locals());
        resolved.subtract(&self.live_locals());
        resolved
    }

    fn resolved_locals_at(&mut self, loc: ExtendedLocation) -> BitSet<Local> {
        trace!("location: {loc:?}");

        if loc.is_entry_loc() {
            // At function entry, no locals are resolved
            // Thus, never live, initialized locals are resolved at mid of the entry location
            return BitSet::new_empty(self.body.local_decls.len());
        }

        self.seek_to(loc);
        self.resolved_locals()
    }

    fn resolved_locals_in_range(
        &mut self,
        start: ExtendedLocation,
        end: ExtendedLocation,
    ) -> BitSet<Local> {
        let resolved_at_start = self.resolved_locals_at(start);
        let resolved_at_end = self.resolved_locals_at(end);

        let mut resolved = resolved_at_end;
        resolved.subtract(&resolved_at_start);
        resolved
    }

    pub fn resolved_locals_during(&mut self, loc: Location) -> BitSet<Local> {
        self.resolved_locals_in_range(ExtendedLocation::Start(loc), ExtendedLocation::Mid(loc))
    }

    /// Only valid if loc is not a terminator.
    pub fn live_locals_after(&mut self, loc: Location) -> BitSet<Local> {
        let next_loc = loc.successor_within_block();
        ExtendedLocation::Start(next_loc).seek_to(&mut self.local_live);
        self.live_locals()
    }

    pub fn frozen_locals_before(&mut self, loc: Location) -> BitSet<Local> {
        ExtendedLocation::Start(loc).seek_to(&mut self.frozen_places);
        self.frozen_locals()
    }

    pub fn resolved_locals_between_blocks(
        &mut self,
        from: BasicBlock,
        to: BasicBlock,
    ) -> BitSet<Local> {
        let term = self.body.terminator_loc(from);
        let start = to.start_location();

        // Some locals are resolved because of the terminator (e.g., a function call) itself.
        // We would like a location which is at the end of the terminator but before branching,
        // but this does not exist. We use the first location of the next block instead.
        let mut resolved = self.resolved_locals_in_range(
            ExtendedLocation::Start(term),
            ExtendedLocation::Start(start),
        );

        // if some locals still need to be resolved at the end of the current block
        // but not at the start of the next block, we also need to resolve them now
        // see the init_join function in the resolve_uninit test
        self.seek_to(ExtendedLocation::Mid(term));
        let need_resolve_at_term = self.need_resolve_locals();
        self.seek_to(ExtendedLocation::Start(start));
        let need_resolve_at_start = self.need_resolve_locals();

        let mut need_resolve = need_resolve_at_term;
        need_resolve.subtract(&need_resolve_at_start);

        resolved.union(&need_resolve);

        resolved
    }

    pub fn need_resolve_locals_before(&mut self, loc: Location) -> BitSet<Local> {
        self.seek_to(ExtendedLocation::Start(loc));
        self.need_resolve_locals()
    }

    #[allow(dead_code)]
    pub(crate) fn debug(&mut self, _regioncx: Rc<RegionInferenceContext<'tcx>>) {
        let body = self.body.clone();
        for (bb, bbd) in traversal::preorder(&body) {
            if bbd.is_cleanup {
                continue;
            }
            eprintln!("{:?}", bb);
            let mut loc = bb.start_location();
            for statement in &bbd.statements {
                self.seek_to(ExtendedLocation::Start(loc));
                let live1 = self.local_live.get().iter().collect::<Vec<_>>();
                let uninit1 = self.local_uninit.get().iter().collect::<Vec<_>>();
                let frozen1 = self.frozen_locals();
                let resolved1 = self.resolved_locals();

                self.seek_to(ExtendedLocation::Mid(loc));
                let live2 = self.local_live.get().iter().collect::<Vec<_>>();
                let uninit2 = self.local_uninit.get().iter().collect::<Vec<_>>();
                let frozen2 = self.frozen_locals();
                let resolved2 = self.resolved_locals();

                eprintln!("  {statement:?} {resolved1:?} -> {resolved2:?}");
                eprintln!(
                    "    live={live1:?} -> {live2:?} frozen={frozen1:?} -> {frozen2:?} uninit={uninit1:?} -> {uninit2:?}",
                );

                loc = loc.successor_within_block();
            }

            self.seek_to(ExtendedLocation::Start(loc));
            let live1 = self.local_live.get().iter().collect::<Vec<_>>();
            let uninit1 = self.local_uninit.get().iter().collect::<Vec<_>>();
            let frozen1 = self.frozen_locals();
            let resolved1 = self.resolved_locals();

            self.seek_to(ExtendedLocation::Mid(loc));
            let live2 = self.local_live.get().iter().collect::<Vec<_>>();
            let uninit2 = self.local_uninit.get().iter().collect::<Vec<_>>();
            let frozen2 = self.frozen_locals();
            let resolved2 = self.resolved_locals();

            eprintln!("  {:?} {resolved1:?} -> {resolved2:?}", bbd.terminator().kind);
            eprintln!(
                "    live={live1:?} -> {live2:?} frozen={frozen1:?} -> {frozen2:?} uninit={uninit1:?} -> {uninit2:?}",
            );
        }
        eprintln!();
    }
}
