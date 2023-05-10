use crate::analysis::{MaybeInitializedLocals, MaybeLiveExceptDrop, MaybeUninitializedLocals};
use rustc_index::bit_set::BitSet;
use rustc_middle::{
    mir::{traversal, BasicBlock, Body, Local, Location},
    ty::TyCtxt,
};
use rustc_mir_dataflow::{Analysis, ResultsCursor};

use crate::extended_location::ExtendedLocation;

pub struct EagerResolver<'body, 'tcx> {
    local_live: ResultsCursor<'body, 'tcx, MaybeLiveExceptDrop>,

    // Whether a local is initialized or not at a location
    local_init: ResultsCursor<'body, 'tcx, MaybeInitializedLocals>,

    local_uninit: ResultsCursor<'body, 'tcx, MaybeUninitializedLocals>,

    body: &'body Body<'tcx>,
}

impl<'body, 'tcx> EagerResolver<'body, 'tcx> {
    pub(crate) fn new(tcx: TyCtxt<'tcx>, body: &'body Body<'tcx>) -> Self {
        let local_init = MaybeInitializedLocals
            .into_engine(tcx, body)
            .iterate_to_fixpoint()
            .into_results_cursor(body);

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

        EagerResolver { local_live, local_init, local_uninit, body }
    }

    fn seek_to(&mut self, loc: ExtendedLocation) {
        loc.seek_to(&mut self.local_live);
        loc.seek_to(&mut self.local_init);
        loc.seek_to(&mut self.local_uninit);
    }

    fn dead_locals(&self) -> BitSet<Local> {
        let mut live: BitSet<_> = BitSet::new_empty(self.body.local_decls.len());
        live.union(self.local_live.get());

        let mut dead: BitSet<_> = BitSet::new_filled(live.domain_size());
        dead.subtract(&live);
        dead
    }

    fn resolved_locals(&self) -> BitSet<Local> {
        let dead = self.dead_locals();

        let init = self.local_init.get().clone();
        let mut uninit: BitSet<_> = BitSet::new_empty(self.body.local_decls.len());
        uninit.union(self.local_uninit.get());

        trace!("dead: {dead:?}");
        trace!("init: {init:?}");
        trace!("uninit: {uninit:?}");

        let mut def_init = init;
        def_init.subtract(&uninit);
        trace!("def_init: {def_init:?}");

        let mut resolved = dead;
        resolved.intersect(&def_init);

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
    pub fn dead_locals_after(&mut self, loc: Location) -> BitSet<Local> {
        let next_loc = loc.successor_within_block();
        ExtendedLocation::Start(next_loc).seek_to(&mut self.local_live);
        self.dead_locals()
    }

    pub fn resolved_locals_between_blocks(
        &mut self,
        from: BasicBlock,
        to: BasicBlock,
    ) -> BitSet<Local> {
        let term = self.body.terminator_loc(from);
        let start = to.start_location();
        self.resolved_locals_in_range(ExtendedLocation::Start(term), ExtendedLocation::Start(start))
    }

    #[allow(dead_code)]
    pub(crate) fn debug(&mut self) {
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
                let init1 = self.local_init.get().clone();
                let uninit1 = self.local_uninit.get().iter().collect::<Vec<_>>();
                let resolved1 = self.resolved_locals();

                self.seek_to(ExtendedLocation::Mid(loc));
                let live2 = self.local_live.get().iter().collect::<Vec<_>>();
                let init2 = self.local_init.get().clone();
                let uninit2 = self.local_uninit.get().iter().collect::<Vec<_>>();
                let resolved2 = self.resolved_locals();

                eprintln!("  {statement:?} {resolved1:?} -> {resolved2:?}");
                if resolved1 != resolved2 {
                    eprintln!(
                        "    live={live1:?} -> {live2:?} init={init1:?} -> {init2:?} uninit={uninit1:?} -> {uninit2:?}",
                    );
                }

                loc = loc.successor_within_block();
            }

            self.seek_to(ExtendedLocation::Start(loc));
            let live1 = self.local_live.get().iter().collect::<Vec<_>>();
            let init1 = self.local_init.get().clone();
            let uninit1 = self.local_uninit.get().iter().collect::<Vec<_>>();
            let resolved1 = self.resolved_locals();

            self.seek_to(ExtendedLocation::Mid(loc));
            let live2 = self.local_live.get().iter().collect::<Vec<_>>();
            let init2 = self.local_init.get().clone();
            let uninit2 = self.local_uninit.get().iter().collect::<Vec<_>>();
            let resolved2 = self.resolved_locals();

            eprintln!("  {:?} {resolved1:?} -> {resolved2:?}", bbd.terminator().kind);
            if resolved1 != resolved2 {
                eprintln!(
                    "    live={live1:?} <- {live2:?} init={init1:?} -> {init2:?} uninit={uninit1:?} -> {uninit2:?}",
                );
            }
        }
        eprintln!();
    }
}
