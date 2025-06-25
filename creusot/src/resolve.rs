use crate::analysis::{Borrows, MaybeLiveExceptDrop};
use either::Either;
use rustc_borrowck::consumers::{BorrowIndex, BorrowSet, PlaceExt, RegionInferenceContext};
use rustc_index::bit_set::MixedBitSet;
use rustc_middle::{
    mir::{
        BasicBlock, Body, Location, PlaceRef, ProjectionElem, Rvalue, Statement, StatementKind,
        TerminatorEdges, traversal,
    },
    ty::{TyCtxt, TyKind},
};
use rustc_mir_dataflow::{
    Analysis, ResultsCursor,
    impls::MaybeUninitializedPlaces,
    move_paths::{HasMoveData, LookupResult, MoveData, MovePathIndex},
    on_all_children_bits,
};

use crate::extended_location::ExtendedLocation;

pub struct Resolver<'a, 'tcx> {
    live: ResultsCursor<'a, 'tcx, MaybeLiveExceptDrop<'a, 'tcx>>,
    uninit: ResultsCursor<'a, 'tcx, MaybeUninitializedPlaces<'a, 'tcx>>,
    borrows: ResultsCursor<'a, 'tcx, Borrows<'a, 'a, 'tcx>>,
    borrow_set: &'a BorrowSet<'tcx>,
    move_data: &'a MoveData<'tcx>,
    body: &'a Body<'tcx>,
    tcx: TyCtxt<'tcx>,
}

impl<'a, 'tcx> HasMoveData<'tcx> for Resolver<'a, 'tcx> {
    fn move_data(&self) -> &MoveData<'tcx> {
        &self.move_data
    }
}

pub trait HasMoveDataExt<'tcx>: HasMoveData<'tcx> {
    fn empty_bitset(&self) -> MixedBitSet<MovePathIndex>;
}

impl<'tcx, T: HasMoveData<'tcx>> HasMoveDataExt<'tcx> for T {
    fn empty_bitset(&self) -> MixedBitSet<MovePathIndex> {
        MixedBitSet::new_empty(self.move_data().move_paths.len())
    }
}

#[derive(Debug)]
struct State {
    live: MixedBitSet<MovePathIndex>,
    uninit: MixedBitSet<MovePathIndex>,
    borrows: MixedBitSet<BorrowIndex>,
}

impl<'a, 'tcx> Resolver<'a, 'tcx> {
    pub(crate) fn new(
        tcx: TyCtxt<'tcx>,
        body: &'a Body<'tcx>,
        borrow_set: &'a BorrowSet<'tcx>,
        regioncx: &'a RegionInferenceContext<'tcx>,
        move_data: &'a MoveData<'tcx>,
    ) -> Resolver<'a, 'tcx> {
        let uninit = MaybeUninitializedPlaces::new(tcx, body, move_data)
            .mark_inactive_variants_as_uninit()
            .iterate_to_fixpoint(tcx, body, None)
            .into_results_cursor(body);

        // MaybeLiveExceptDrop ignores `drop` for the purpose of resolve liveness... unclear that this can
        // be sound.
        let live = MaybeLiveExceptDrop::new(tcx, body, move_data)
            .iterate_to_fixpoint(tcx, body, None)
            .into_results_cursor(body);

        let borrows = Borrows::new(tcx, body, &regioncx, borrow_set)
            .iterate_to_fixpoint(tcx, body, None)
            .into_results_cursor(body);

        Resolver { live, uninit, borrows, borrow_set, move_data, body, tcx }
    }

    /// Get the set of frozen move paths corresponding to the given set of borrows.
    /// If both components of a tuple are borrowed, then each component is
    /// considered frozen independently, and not the parent move path.
    fn frozen_of_borrows(&self, borrows: &MixedBitSet<BorrowIndex>) -> MixedBitSet<MovePathIndex> {
        let mut frozen = self.empty_bitset();
        for bi in borrows.iter() {
            let place = self.borrow_set[bi].borrowed_place();
            match self.move_data().rev_lookup.find(place.as_ref()) {
                LookupResult::Exact(mp) => on_all_children_bits(&self.move_data(), mp, |mp| {
                    frozen.insert(mp);
                }),
                LookupResult::Parent(mp) => drop(frozen.insert(mp.unwrap())),
            };
        }
        frozen
    }

    /// Places that need to be resolved eventually
    /// = (live ∪ frozen) ∩ initialized
    fn need_resolve_places(&self, st: &State) -> MixedBitSet<MovePathIndex> {
        let mut should_resolve = self.frozen_of_borrows(&st.borrows);
        should_resolve.union(&st.live);
        should_resolve.subtract(&st.uninit);
        should_resolve
    }

    /// Places that have already been resolved
    /// = not live ∩ not frozen ∩ initialized
    /// = initialized - need_resolve_places
    fn resolved_places(&self, st: &State) -> MixedBitSet<MovePathIndex> {
        let mut x = self.frozen_of_borrows(&st.borrows);
        x.union(&st.live);
        x.union(&st.uninit);

        let mut resolved = self.empty_bitset();
        resolved.insert_all();
        resolved.subtract(&x);
        resolved
    }

    /// This function computes resolver state corresponding to the given extended location.
    /// It forwards the query to the underlying analyses, but treats specially two cases, by manually
    /// an partially applying parts of the transfer functions.
    ///    - If we ask for the mid state of a statement, then this statement is required to
    ///      be an assignment. In this case, we manually compute the state after RHS is evaluated
    ///      but before LHS is assigned (this more or less matches the mid state for a function call).
    ///    - If we ask to the end state of a terminator, then this statement is required to be a function
    ///      call. In this case, we manually compute the state after the assignement of the return place, but
    ///      before joining with other edges that would end up in the same block.
    fn state_at_loc(&mut self, loc: ExtendedLocation) -> State {
        let (mut uninit, mut live, mut borrows);
        match loc {
            ExtendedLocation::Mid(loc) if self.body.stmt_at(loc).is_left() => {
                // TODO: this is copying bits of the various analyses. Move this there,
                // and factor what can be factored.
                self.uninit.seek_before_primary_effect(loc);
                uninit = self.uninit.get().clone();
                for mi in &self.move_data().loc_map[loc] {
                    let path = mi.move_path_index(self.move_data());
                    on_all_children_bits(self.move_data(), path, |mpi| {
                        uninit.insert(mpi);
                    })
                }

                self.live.seek_before_primary_effect(loc);
                live = self.live.get().clone();
                let lhs_pl = match self.body.stmt_at(loc).left() {
                    Some(Statement { kind: StatementKind::Assign(box (pl, _)), .. }) => pl,
                    _ => unreachable!(),
                };
                match self.move_data().rev_lookup.find(lhs_pl.as_ref()) {
                    LookupResult::Exact(mp) => on_all_children_bits(self.move_data(), mp, |mpi| {
                        live.remove(mpi);
                    }),
                    LookupResult::Parent(Some(mp)) => {
                        if place_contains_borrow_deref(lhs_pl.as_ref(), self.body, self.tcx) {
                            live.insert(mp);
                        }
                    }
                    LookupResult::Parent(None) => unreachable!(),
                }

                self.borrows.seek_before_primary_effect(loc);
                borrows = self.borrows.get().clone();
                if let Some(indices) =
                    self.borrows.analysis().borrows_out_of_scope_at_location.get(&loc)
                {
                    for bi in indices {
                        borrows.remove(*bi);
                    }
                }
                if let Some(Statement {
                    kind: StatementKind::Assign(box (_, Rvalue::Ref(_, _, place))),
                    ..
                }) = self.body.stmt_at(loc).left()
                {
                    if !place.ignore_borrow(
                        self.tcx,
                        self.body,
                        &self.borrow_set.locals_state_at_exit(),
                    ) {
                        let index = BorrowIndex::from(
                            self.borrow_set.location_map().get_index_of(&loc).unwrap(),
                        );
                        borrows.insert(index);
                    }
                }
            }
            ExtendedLocation::End(loc) if let Either::Right(term) = self.body.stmt_at(loc) => {
                if let TerminatorEdges::AssignOnReturn { return_, place, .. } = term.edges() {
                    self.uninit.seek_after_primary_effect(loc);
                    uninit = self.uninit.get().clone();
                    self.uninit.mut_analysis().apply_call_return_effect(
                        &mut uninit,
                        loc.block,
                        place,
                    );

                    self.borrows.seek_before_primary_effect(loc);
                    borrows = self.borrows.get().clone();
                    self.borrows.mut_analysis().apply_call_return_effect(
                        &mut borrows,
                        loc.block,
                        place,
                    );

                    if return_.len() == 1 {
                        self.live.seek_after_primary_effect(return_[0].start_location());
                        live = self.live.get().clone();
                    } else {
                        assert_eq!(return_.len(), 0);
                        live = MixedBitSet::new_empty(self.move_data().move_paths.len());
                    }
                } else {
                    return self.state_at_loc(ExtendedLocation::Mid(loc));
                }
            }
            _ => {
                loc.seek_to(&mut self.uninit);
                uninit = self.uninit.get().clone();

                loc.seek_to(&mut self.live);
                live = self.live.get().clone();

                loc.seek_to(&mut self.borrows);
                borrows = self.borrows.get().clone();
            }
        }
        State { uninit, live, borrows }
    }

    pub fn need_resolve_resolved_places_at(
        &mut self,
        loc: ExtendedLocation,
    ) -> (MixedBitSet<MovePathIndex>, MixedBitSet<MovePathIndex>) {
        let st = self.state_at_loc(loc);
        (self.need_resolve_places(&st), self.resolved_places(&st))
    }

    pub fn resolved_places_during(
        &mut self,
        loc: ExtendedLocation,
    ) -> (MixedBitSet<MovePathIndex>, MixedBitSet<MovePathIndex>) {
        let (mut res, resolved) =
            self.need_resolve_resolved_places_at(ExtendedLocation::Start(loc.loc()));
        let st_after = self.state_at_loc(loc);

        // MixedBitSet::intersect is not implemented in rustc, substract is...
        //res.intersect(&self.resolved_places(&st_after));
        let mut not_res = res.clone();
        not_res.subtract(&self.resolved_places(&st_after));
        res.subtract(&not_res);

        (res, resolved)
    }

    pub fn resolved_places_between_blocks(
        &mut self,
        from: BasicBlock,
        to: BasicBlock,
    ) -> (MixedBitSet<MovePathIndex>, MixedBitSet<MovePathIndex>) {
        // if some places still need to be resolved at the end of the current block
        // but not at the start of the next block, we also need to resolve them now
        // see the init_join function in the resolve_uninit test

        let from_loc = ExtendedLocation::End(self.body.terminator_loc(from));
        let to_loc = ExtendedLocation::Start(to.start_location());

        let state_from = self.state_at_loc(from_loc);
        let state_to = self.state_at_loc(to_loc);

        let mut res = self.need_resolve_places(&state_from);
        res.subtract(&self.need_resolve_places(&state_to));

        (res, self.resolved_places(&state_from))
    }

    pub fn uninit_places_before(&mut self, loc: Location) -> MixedBitSet<MovePathIndex> {
        ExtendedLocation::Start(loc).seek_to(&mut self.uninit);
        self.uninit.get().clone()
    }

    pub fn live_places_before(&mut self, loc: Location) -> MixedBitSet<MovePathIndex> {
        ExtendedLocation::Start(loc).seek_to(&mut self.live);
        self.live.get().clone()
    }

    pub fn frozen_places_before(&mut self, loc: Location) -> MixedBitSet<MovePathIndex> {
        ExtendedLocation::Start(loc).seek_to(&mut self.borrows);
        self.frozen_of_borrows(self.borrows.get())
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
                let state1 = self.state_at_loc(ExtendedLocation::Start(loc));
                let live1 = state1.live.iter().collect::<Vec<_>>();
                let uninit1 = state1.uninit.iter().collect::<Vec<_>>();
                let frozen1 = self.frozen_of_borrows(&state1.borrows).iter().collect::<Vec<_>>();
                let need_resolve1 = self.need_resolve_places(&state1);

                let state2 = self.state_at_loc(ExtendedLocation::End(loc));
                let live2 = state2.live.iter().collect::<Vec<_>>();
                let uninit2 = state2.uninit.iter().collect::<Vec<_>>();
                let frozen2 = self.frozen_of_borrows(&state2.borrows).iter().collect::<Vec<_>>();
                let resolved2 = self.resolved_places(&state2);

                eprintln!("  {statement:?} {need_resolve1:?} -> {resolved2:?}");
                eprintln!(
                    "    live={live1:?} -> {live2:?} frozen={frozen1:?} -> {frozen2:?} uninit={uninit1:?} -> {uninit2:?}",
                );

                loc = loc.successor_within_block();
            }

            let state1 = self.state_at_loc(ExtendedLocation::Start(loc));
            let live1 = state1.live.iter().collect::<Vec<_>>();
            let uninit1 = state1.uninit.iter().collect::<Vec<_>>();
            let frozen1 = self.frozen_of_borrows(&state1.borrows).iter().collect::<Vec<_>>();
            let need_resolve1 = self.need_resolve_places(&state1);

            let state2 = self.state_at_loc(ExtendedLocation::End(loc));
            let live2 = state2.live.iter().collect::<Vec<_>>();
            let uninit2 = state2.uninit.iter().collect::<Vec<_>>();
            let frozen2 = self.frozen_of_borrows(&state2.borrows).iter().collect::<Vec<_>>();
            let resolved2 = self.resolved_places(&state2);

            eprintln!("  {:?} {need_resolve1:?} -> {resolved2:?}", bbd.terminator().kind);
            eprintln!(
                "    live={live1:?} -> {live2:?} frozen={frozen1:?} -> {frozen2:?} uninit={uninit1:?} -> {uninit2:?}",
            );
        }
        eprintln!();
    }
}

pub fn place_contains_borrow_deref<'tcx>(
    place: PlaceRef<'tcx>,
    body: &Body<'tcx>,
    tcx: TyCtxt<'tcx>,
) -> bool {
    place.iter_projections().any(|(pl, proj)| {
        proj == ProjectionElem::Deref
            && matches!(pl.ty(&body.local_decls, tcx).ty.kind(), TyKind::Ref(..))
    })
}
