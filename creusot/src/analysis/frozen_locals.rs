use std::{fmt, rc::Rc};

use dataflow::fmt::DebugWithContext;
use rustc_borrowck::{
    borrow_set::BorrowSet,
    consumers::{BorrowIndex, PlaceConflictBias, PlaceExt},
};
use rustc_data_structures::fx::FxIndexMap;
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.
//
use rustc_index::bit_set::BitSet;
use rustc_middle::{
    mir::{self, Body, CallReturnPlaces, Location, Place, TerminatorEdges},
    ty::TyCtxt,
};
use rustc_mir_dataflow::{self as dataflow, GenKill};

pub struct Borrows<'body, 'tcx> {
    tcx: TyCtxt<'tcx>,
    body: &'body Body<'tcx>,
    borrow_set: Rc<BorrowSet<'tcx>>,
    borrows_out_of_scope_at_location: FxIndexMap<Location, Vec<BorrowIndex>>,
}

impl<'body, 'tcx> Borrows<'body, 'tcx> {
    pub fn new(
        tcx: TyCtxt<'tcx>,
        body: &'body Body<'tcx>,
        borrow_set: Rc<BorrowSet<'tcx>>,
        borrows_out_of_scope_at_location: FxIndexMap<Location, Vec<BorrowIndex>>,
    ) -> Self {
        Borrows { tcx, body, borrow_set, borrows_out_of_scope_at_location }
    }

    pub fn location(&self, idx: BorrowIndex) -> &Location {
        &self.borrow_set[idx].reserve_location
    }

    /// Add all borrows to the kill set, if those borrows are out of scope at `location`.
    /// That means they went out of a nonlexical scope
    fn kill_loans_out_of_scope_at_location(
        &self,
        trans: &mut impl GenKill<BorrowIndex>,
        location: Location,
    ) {
        // NOTE: The state associated with a given `location`
        // reflects the dataflow on entry to the statement.
        // Iterate over each of the borrows that we've precomputed
        // to have went out of scope at this location and kill them.
        //
        // We are careful always to call this function *before* we
        // set up the gen-bits for the statement or
        // terminator. That way, if the effect of the statement or
        // terminator *does* introduce a new loan of the same
        // region, then setting that gen-bit will override any
        // potential kill introduced here.
        if let Some(indices) = self.borrows_out_of_scope_at_location.get(&location) {
            trans.kill_all(indices.iter().copied());
        }
    }

    /// Kill any borrows that conflict with `place`.
    fn kill_borrows_on_place(&self, trans: &mut impl GenKill<BorrowIndex>, place: Place<'tcx>) {
        debug!("kill_borrows_on_place: place={:?}", place);

        let other_borrows_of_local = self
            .borrow_set
            .local_map
            .get(&place.local)
            .into_iter()
            .flat_map(|bs| bs.iter())
            .copied();

        // If the borrowed place is a local with no projections, all other borrows of this
        // local must conflict. This is purely an optimization so we don't have to call
        // `places_conflict` for every borrow.
        if place.projection.is_empty() {
            if !self.body.local_decls[place.local].is_ref_to_static() {
                trans.kill_all(other_borrows_of_local);
            }
            return;
        }

        // By passing `PlaceConflictBias::NoOverlap`, we conservatively assume that any given
        // pair of array indices are unequal, so that when `places_conflict` returns true, we
        // will be assured that two places being compared definitely denotes the same sets of
        // locations.
        let definitely_conflicting_borrows = other_borrows_of_local.filter(|&i| {
            rustc_borrowck::consumers::places_conflict(
                self.tcx,
                self.body,
                self.borrow_set[i].borrowed_place,
                place,
                PlaceConflictBias::NoOverlap,
            )
        });

        trans.kill_all(definitely_conflicting_borrows);
    }
}

impl<'tcx> dataflow::AnalysisDomain<'tcx> for Borrows<'_, 'tcx> {
    type Domain = BitSet<BorrowIndex>;

    const NAME: &'static str = "borrows";

    fn bottom_value(&self, _: &mir::Body<'tcx>) -> Self::Domain {
        // bottom = nothing is reserved or activated yet;
        BitSet::new_empty(self.borrow_set.len() * 2)
    }

    fn initialize_start_block(&self, _: &mir::Body<'tcx>, _: &mut Self::Domain) {
        // no borrows of code region_scopes have been taken prior to
        // function execution, so this method has no effect.
    }
}

impl<'tcx> dataflow::GenKillAnalysis<'tcx> for Borrows<'_, 'tcx> {
    type Idx = BorrowIndex;

    fn before_statement_effect(
        &mut self,
        _trans: &mut impl GenKill<Self::Idx>,
        _statement: &mir::Statement<'tcx>,
        _location: Location,
    ) {
    }

    fn statement_effect(
        &mut self,
        trans: &mut impl GenKill<Self::Idx>,
        stmt: &mir::Statement<'tcx>,
        location: Location,
    ) {
        self.kill_loans_out_of_scope_at_location(trans, location);

        match &stmt.kind {
            mir::StatementKind::Assign(box (lhs, rhs)) => {
                if let mir::Rvalue::Ref(_, _, place) = rhs {
                    if place.ignore_borrow(
                        self.tcx,
                        self.body,
                        &self.borrow_set.locals_state_at_exit,
                    ) {
                        return;
                    }
                    let index = self
                        .borrow_set
                        .location_map
                        .get_index_of(&location)
                        .map(BorrowIndex::from)
                        .unwrap_or_else(|| {
                            panic!("could not find BorrowIndex for location {:?}", location);
                        });

                    trans.gen(index);
                }

                // Make sure there are no remaining borrows for variables
                // that are assigned over.
                self.kill_borrows_on_place(trans, *lhs);
            }

            mir::StatementKind::StorageDead(local) => {
                // Make sure there are no remaining borrows for locals that
                // are gone out of scope.
                self.kill_borrows_on_place(trans, Place::from(*local));
            }

            mir::StatementKind::FakeRead(..)
            | mir::StatementKind::SetDiscriminant { .. }
            | mir::StatementKind::Deinit(..)
            | mir::StatementKind::StorageLive(..)
            | mir::StatementKind::Retag { .. }
            | mir::StatementKind::PlaceMention(..)
            | mir::StatementKind::AscribeUserType(..)
            | mir::StatementKind::Coverage(..)
            | mir::StatementKind::Intrinsic(..)
            | mir::StatementKind::ConstEvalCounter
            | mir::StatementKind::Nop => {}
        }
    }

    fn before_terminator_effect(
        &mut self,
        _trans: &mut Self::Domain,
        _terminator: &mir::Terminator<'tcx>,
        _location: Location,
    ) {
    }

    fn terminator_effect<'mir>(
        &mut self,
        trans: &mut Self::Domain,
        terminator: &'mir mir::Terminator<'tcx>,
        location: Location,
    ) -> TerminatorEdges<'mir, 'tcx> {
        self.kill_loans_out_of_scope_at_location(trans, location);

        if let mir::TerminatorKind::InlineAsm { operands, .. } = &terminator.kind {
            for op in operands {
                if let mir::InlineAsmOperand::Out { place: Some(place), .. }
                | mir::InlineAsmOperand::InOut { out_place: Some(place), .. } = *op
                {
                    self.kill_borrows_on_place(trans, place);
                }
            }
        }
        terminator.edges()
    }

    fn call_return_effect(
        &mut self,
        _trans: &mut Self::Domain,
        _block: mir::BasicBlock,
        _return_places: CallReturnPlaces<'_, 'tcx>,
    ) {
    }

    fn domain_size(&self, _: &mir::Body<'tcx>) -> usize {
        self.borrow_set.len() * 2
    }
}

impl DebugWithContext<Borrows<'_, '_>> for BorrowIndex {
    fn fmt_with(&self, ctxt: &Borrows<'_, '_>, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{:?}", ctxt.location(*self))
    }
}
