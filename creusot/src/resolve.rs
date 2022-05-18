use std::rc::Rc;

use crate::analysis::uninit_locals::MaybeUninitializedLocals;
use rustc_borrowck::borrow_set::{BorrowSet, TwoPhaseActivation};
use rustc_index::bit_set::BitSet;
use tool_lib::{
    mir::{BasicBlock, Body, Local, Location},
    ty::TyCtxt,
};
use rustc_mir_dataflow::{
    self,
    impls::{MaybeInitializedLocals, MaybeLiveLocals},
    Analysis, ResultsCursor,
};

use crate::extended_location::ExtendedLocation;

pub struct EagerResolver<'body, 'tcx> {
    local_live: ResultsCursor<'body, 'tcx, MaybeLiveLocals>,

    // Whether a local is initialized or not at a location
    local_init: ResultsCursor<'body, 'tcx, MaybeInitializedLocals>,

    local_uninit: ResultsCursor<'body, 'tcx, MaybeUninitializedLocals>,

    // Locals that are never read
    never_live: BitSet<Local>,

    body: &'body Body<'tcx>,

    borrows: Rc<BorrowSet<'tcx>>,
}

impl<'body, 'tcx> EagerResolver<'body, 'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>, body: &'body Body<'tcx>, borrows: Rc<BorrowSet<'tcx>>) -> Self {
        let local_init = MaybeInitializedLocals
            .into_engine(tcx, body)
            .iterate_to_fixpoint()
            .into_results_cursor(body);

        let local_uninit = MaybeUninitializedLocals
            .into_engine(tcx, body)
            .iterate_to_fixpoint()
            .into_results_cursor(body);

        // This is called MaybeLiveLocals because pointers don't keep their referees alive.
        // TODO: Defensive check.
        let local_live =
            MaybeLiveLocals.into_engine(tcx, body).iterate_to_fixpoint().into_results_cursor(body);
        let never_live = crate::analysis::NeverLive::for_body(body);
        EagerResolver { local_live, local_init, local_uninit, never_live, body, borrows }
    }

    fn unactivated_borrows(&self, loc: Location) -> BitSet<Local> {
        let dom = self.body.dominators();

        let mut bits = BitSet::new_empty(self.body.local_decls.len());

        self.borrows
            .location_map
            .iter()
            .filter(|(_, bd)| {
                let res_loc = bd.reserve_location;
                if res_loc.block == loc.block {
                    res_loc.statement_index <= loc.statement_index
                } else {
                    dom.is_dominated_by(loc.block, res_loc.block)
                }
            })
            .filter(|(_, bd)| {
                if let TwoPhaseActivation::ActivatedAt(act_loc) = bd.activation_location {
                    if act_loc.block == loc.block {
                        loc.statement_index <= act_loc.statement_index
                    } else {
                        dom.is_dominated_by(act_loc.block, loc.block)
                    }
                } else {
                    false
                }
            })
            .for_each(|(_, bd)| {
                bits.insert(bd.borrowed_place.local);
            });

        bits
    }

    pub fn locals_resolved_at_loc(&mut self, loc: Location) -> BitSet<Local> {
        self.locals_resolved_between(
            ExtendedLocation::Start(loc),
            ExtendedLocation::Mid(loc),
            loc,
            loc.successor_within_block(),
        )
    }

    pub fn locals_resolved_between_blocks(
        &mut self,
        from: BasicBlock,
        to: BasicBlock,
    ) -> BitSet<Local> {
        let term = self.body.terminator_loc(from);
        let start = to.start_location();

        self.locals_resolved_between(
            ExtendedLocation::Start(term),
            ExtendedLocation::Start(start),
            term,
            start,
        )
    }

    fn locals_resolved_between(
        &mut self,
        start: ExtendedLocation,
        end: ExtendedLocation,
        two_phase_start: Location,
        two_phase_end: Location,
    ) -> BitSet<Local> {
        start.seek_to(&mut self.local_live);
        let mut live_at_start = self.local_live.get().clone();
        if start.is_entry_loc() {
            // Count arguments that were never live as live here
            live_at_start.union(&self.never_live);
        }

        live_at_start.union(&self.unactivated_borrows(two_phase_start));

        end.seek_to(&mut self.local_live);
        let mut live_at_end = self.local_live.get().clone();
        live_at_end.union(&self.unactivated_borrows(two_phase_end));

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
        trace!("def_init_at_start: {:?}", def_init_at_start);

        let mut def_init_at_end = init_at_end.clone();
        def_init_at_end.subtract(&uninit_at_end);
        trace!("def_init_at_end: {:?}", def_init_at_end);
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
        zombies.subtract(&live_at_end);
        trace!("zombies: {:?}", zombies);

        let mut dying = live_at_start;

        // Variables that died in the span
        dying.subtract(&live_at_end);
        // And were initialized
        let mut init = def_init_at_start;
        init.intersect(&def_init_at_end);
        dying.intersect(&init);

        // dying.subtract(&unactivated);

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
