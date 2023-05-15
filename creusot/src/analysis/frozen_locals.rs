use std::rc::Rc;

use borrowck::{borrow_set::BorrowSet, dataflow::BorrowIndex};
use rustc_data_structures::fx::FxIndexMap;
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.
//
use rustc_index::bit_set::BitSet;
use rustc_middle::mir::{self, Local, Location};
use rustc_mir_dataflow::{self as dataflow, AnalysisDomain, GenKill};

pub struct MaybeFrozenLocals<'tcx> {
    borrow_set: Rc<BorrowSet<'tcx>>,
    borrows_out_of_scope_at_location: FxIndexMap<Location, Vec<BorrowIndex>>,
}

impl<'tcx> AnalysisDomain<'tcx> for MaybeFrozenLocals<'tcx> {
    type Domain = BitSet<Local>;

    const NAME: &'static str = "frozen_locals";

    fn bottom_value(&self, body: &mir::Body<'tcx>) -> Self::Domain {
        // bottom = uninit
        BitSet::new_empty(body.local_decls.len())
    }

    fn initialize_start_block(&self, _: &mir::Body<'tcx>, _: &mut Self::Domain) {}
}

impl<'tcx> MaybeFrozenLocals<'tcx> {
    pub fn new(
        borrow_set: Rc<BorrowSet<'tcx>>,
        borrows_out_of_scope_at_location: FxIndexMap<Location, Vec<BorrowIndex>>,
    ) -> Self {
        MaybeFrozenLocals { borrow_set, borrows_out_of_scope_at_location }
    }

    fn kill_loans_out_of_scope_at_location(
        &self,
        trans: &mut impl GenKill<Local>,
        location: Location,
    ) {
        if let Some(indices) = self.borrows_out_of_scope_at_location.get(&location) {
            trans.kill_all(indices.iter().map(|bi| self.borrow_set[*bi].borrowed_place.local));
        }
    }
}

impl<'tcx> dataflow::GenKillAnalysis<'tcx> for MaybeFrozenLocals<'tcx> {
    type Idx = Local;

    fn before_statement_effect(
        &self,
        _trans: &mut impl GenKill<Self::Idx>,
        _statement: &mir::Statement<'tcx>,
        _location: Location,
    ) {
        // self.kill_loans_out_of_scope_at_location(trans, location);
    }

    fn statement_effect(
        &self,
        trans: &mut impl GenKill<Self::Idx>,
        stmt: &mir::Statement<'tcx>,
        location: Location,
    ) {
        self.kill_loans_out_of_scope_at_location(trans, location);
        match &stmt.kind {
            mir::StatementKind::Assign(box (lhs, rhs)) => {
                if let mir::Rvalue::Ref(_, _, place) = rhs {
                    // check place.ignore_borrow?
                    trans.gen(place.local);
                }

                // kill assigned-over local
                trans.kill(lhs.local);
            }

            mir::StatementKind::StorageDead(local) => {
                // kill out-of-scope local
                trans.kill(*local);
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
        &self,
        _trans: &mut impl GenKill<Self::Idx>,
        _terminator: &mir::Terminator<'tcx>,
        _location: Location,
    ) {
        // self.kill_loans_out_of_scope_at_location(trans, location);
    }

    fn terminator_effect(
        &self,
        trans: &mut impl GenKill<Self::Idx>,
        _terminator: &mir::Terminator<'tcx>,
        location: Location,
    ) {
        self.kill_loans_out_of_scope_at_location(trans, location);
    }

    fn call_return_effect(
        &self,
        _trans: &mut impl GenKill<Self::Idx>,
        _block: mir::BasicBlock,
        _return_places: dataflow::CallReturnPlaces<'_, 'tcx>,
    ) {
    }
}
