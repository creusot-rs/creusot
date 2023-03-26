// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.
//
use rustc_index::bit_set::ChunkedBitSet;
use rustc_middle::mir::{
    self,
    visit::{PlaceContext, Visitor},
    BasicBlock, Local, Location, Terminator,
};
use rustc_mir_dataflow::{self as dataflow, AnalysisDomain, GenKill, GenKillAnalysis};

pub struct MaybeUninitializedLocals;

impl<'tcx> AnalysisDomain<'tcx> for MaybeUninitializedLocals {
    type Domain = ChunkedBitSet<Local>;

    const NAME: &'static str = "maybe_uninit_locals";

    fn bottom_value(&self, body: &mir::Body<'tcx>) -> Self::Domain {
        // bottom = init
        ChunkedBitSet::new_empty(body.local_decls.len())
    }

    fn initialize_start_block(&self, body: &mir::Body<'tcx>, entry_set: &mut Self::Domain) {
        entry_set.insert_all();

        for arg in body.args_iter() {
            entry_set.remove(arg);
        }
    }
}

impl<'tcx> GenKillAnalysis<'tcx> for MaybeUninitializedLocals {
    type Idx = Local;

    fn statement_effect(
        &self,
        trans: &mut impl GenKill<Self::Idx>,
        statement: &mir::Statement<'tcx>,
        loc: Location,
    ) {
        TransferFunction { trans }.visit_statement(statement, loc)
    }

    fn terminator_effect(
        &self,
        trans: &mut impl GenKill<Self::Idx>,
        terminator: &Terminator<'tcx>,
        loc: Location,
    ) {
        TransferFunction { trans }.visit_terminator(terminator, loc)
    }

    fn call_return_effect(
        &self,
        trans: &mut impl GenKill<Self::Idx>,
        _block: BasicBlock,
        return_places: dataflow::CallReturnPlaces<'_, 'tcx>,
    ) {
        return_places.for_each(|place| {
            if let Some(local) = place.as_local() {
                trans.kill(local);
            }
        });
    }

    /// See `Analysis::apply_yield_resume_effect`.
    fn yield_resume_effect(
        &self,
        trans: &mut impl GenKill<Self::Idx>,
        _resume_block: BasicBlock,
        resume_place: mir::Place<'tcx>,
    ) {
        trans.kill(resume_place.local)
    }
}

struct TransferFunction<'a, T> {
    trans: &'a mut T,
}

impl<'a, 'tcx, T> Visitor<'tcx> for TransferFunction<'a, T>
where
    T: GenKill<Local>,
{
    fn visit_local(&mut self, local: Local, context: PlaceContext, _: Location) {
        use rustc_middle::mir::visit::{MutatingUseContext, NonMutatingUseContext, NonUseContext};
        match context {
            // These are handled specially in `call_return_effect` and `yield_resume_effect`.
            PlaceContext::MutatingUse(MutatingUseContext::Call | MutatingUseContext::Yield) => {}

            // Otherwise, when a place is mutated, we must consider it possibly initialized.
            PlaceContext::MutatingUse(_) => self.trans.kill(local),

            // If the local is moved out of, or if it gets marked `StorageDead`, consider it no
            // longer initialized.
            PlaceContext::NonUse(NonUseContext::StorageDead)
            | PlaceContext::NonMutatingUse(NonMutatingUseContext::Move) => self.trans.gen(local),

            // All other uses do not affect this analysis.
            PlaceContext::NonUse(
                NonUseContext::StorageLive
                | NonUseContext::AscribeUserTy
                | NonUseContext::VarDebugInfo
                | NonUseContext::PlaceMention,
            )
            | PlaceContext::NonMutatingUse(
                NonMutatingUseContext::Inspect
                | NonMutatingUseContext::Copy
                | NonMutatingUseContext::SharedBorrow
                | NonMutatingUseContext::ShallowBorrow
                | NonMutatingUseContext::UniqueBorrow
                | NonMutatingUseContext::AddressOf
                | NonMutatingUseContext::Projection,
            ) => {}
        }
    }
}
