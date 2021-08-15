use crate::analysis::uninit_locals::MaybeUninitializedLocals;
use rustc_index::bit_set::BitSet;
use rustc_middle::{
    mir::{Body, Local},
    ty::TyCtxt,
};
use rustc_mir::dataflow::{
    self,
    impls::{MaybeInitializedLocals, MaybeLiveLocals},
    Analysis,
};

use crate::extended_location::ExtendedLocation;

pub struct EagerResolver<'body, 'tcx> {
    local_live: dataflow::ResultsCursor<'body, 'tcx, MaybeLiveLocals>,

    // Whether a local is initialized or not at a location
    local_init: dataflow::ResultsCursor<'body, 'tcx, MaybeInitializedLocals>,

    local_uninit: dataflow::ResultsCursor<'body, 'tcx, MaybeUninitializedLocals>,

    // Locals that are never read
    never_live: BitSet<Local>,
}

impl<'body, 'tcx> EagerResolver<'body, 'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>, body: &'body Body<'tcx>) -> Self {
        let local_init = MaybeInitializedLocals
            .into_engine(tcx, &body)
            .iterate_to_fixpoint()
            .into_results_cursor(&body);

        let local_uninit = MaybeUninitializedLocals
            .into_engine(tcx, &body)
            .iterate_to_fixpoint()
            .into_results_cursor(&body);

        // This is called MaybeLiveLocals because pointers don't keep their referees alive.
        // TODO: Defensive check.
        let local_live = MaybeLiveLocals
            .into_engine(tcx, &body)
            .iterate_to_fixpoint()
            .into_results_cursor(&body);
        let never_live = crate::analysis::NeverLive::for_body(body);
        EagerResolver { local_live, local_init, local_uninit, never_live }
    }

    pub fn locals_resolved_between(
        &mut self,
        start: ExtendedLocation,
        end: ExtendedLocation,
    ) -> BitSet<Local> {
        start.seek_to(&mut self.local_live);
        let mut live_at_start = self.local_live.get().clone();
        if start.is_entry_loc() {
            // Count arguments that were never live as live here
            live_at_start.union(&self.never_live);
        }

        end.seek_to(&mut self.local_live);
        let live_at_end = self.local_live.get();

        start.seek_to(&mut self.local_init);
        let init_at_start = self.local_init.get().clone();

        end.seek_to(&mut self.local_init);
        let init_at_end = self.local_init.get().clone();

        start.seek_to(&mut self.local_uninit);
        let uninit_at_start = self.local_uninit.get().clone();

        end.seek_to(&mut self.local_uninit);
        let uninit_at_end = self.local_uninit.get().clone();

        trace!("location: {:?}-{:?}", start, end);
        trace!("live_at_start: {:?}", live_at_start);
        trace!("live_at_end: {:?}", live_at_end);
        trace!("init_at_start: {:?}", init_at_start);
        trace!("init_at_end: {:?}", init_at_end);
        trace!("uninit_at_start: {:?}", uninit_at_start);
        trace!("uninit_at_end: {:?}", uninit_at_end);

        let mut def_init_at_start = init_at_start;
        def_init_at_start.subtract(&uninit_at_start);

        // Locals that were just now initialized
        let mut just_init = init_at_end.clone();
        just_init.subtract(&uninit_at_end);

        just_init.subtract(&def_init_at_start);
        trace!("just_init: {:?}", just_init);

        // Locals that have just become live
        let mut born = live_at_end.clone();
        born.subtract(&live_at_start);
        trace!("born: {:?}", born);

        // Locals that were initialized but never live
        let mut zombies = just_init.clone();
        zombies.subtract(live_at_end);
        trace!("zombies: {:?}", zombies);

        let mut dying = live_at_start;

        // Variables that died in the span
        dying.subtract(live_at_end);
        // And were initialized
        dying.intersect(&def_init_at_start);

        let same_point = start.same_block(end);
        trace!("same_block: {:?}", same_point);
        // But if we created a new value or brought one back to life
        if (!just_init.is_empty() && same_point) || !born.is_empty() {
            // Exclude values that were moved
            dying.intersect(&init_at_end);
            // And include the values that never made it past their creation
            dying.union(&zombies);
        }

        trace!("dying: {:?}", dying);

        dying
    }
}
