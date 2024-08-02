// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.
//
use dataflow::Backward;
use rustc_index::bit_set::ChunkedBitSet;
use rustc_middle::mir::{
    self,
    visit::{MutatingUseContext, NonMutatingUseContext, PlaceContext, Visitor},
    CallReturnPlaces, Local, Location, Place, TerminatorEdges,
};
use rustc_mir_dataflow::{self as dataflow, AnalysisDomain, GenKill, GenKillAnalysis};

/// A liveness analysis which ignores `drop`. This is meant to be used exclusively for `Resolve`.
/// FIXME: Replace this if any unsoundness seems to occur with borrows.
pub struct MaybeLiveExceptDrop;

impl<'tcx> AnalysisDomain<'tcx> for MaybeLiveExceptDrop {
    type Domain = ChunkedBitSet<Local>;
    type Direction = Backward;

    const NAME: &'static str = "liveness-two";

    fn bottom_value(&self, body: &mir::Body<'tcx>) -> Self::Domain {
        // bottom = not live
        ChunkedBitSet::new_empty(body.local_decls.len())
    }

    fn initialize_start_block(&self, _: &mir::Body<'tcx>, _: &mut Self::Domain) {
        // No variables are live until we observe a use
    }
}

impl<'tcx> GenKillAnalysis<'tcx> for MaybeLiveExceptDrop {
    type Idx = Local;

    fn statement_effect(
        &mut self,
        trans: &mut impl GenKill<Self::Idx>,
        statement: &mir::Statement<'tcx>,
        location: Location,
    ) {
        TransferFunction(trans).visit_statement(statement, location);
    }

    fn terminator_effect<'mir>(
        &mut self,
        trans: &mut Self::Domain,
        terminator: &'mir mir::Terminator<'tcx>,
        location: Location,
    ) -> TerminatorEdges<'mir, 'tcx> {
        TransferFunction(trans).visit_terminator(terminator, location);
        terminator.edges()
    }

    fn call_return_effect(
        &mut self,
        trans: &mut Self::Domain,
        _block: mir::BasicBlock,
        return_places: CallReturnPlaces<'_, 'tcx>,
    ) {
        return_places.for_each(|place| {
            if let Some(local) = place.as_local() {
                trans.kill(local);
            }
        });
    }

    fn domain_size(&self, body: &mir::Body<'tcx>) -> usize {
        body.local_decls.len()
    }
}

struct TransferFunction<'a, T>(&'a mut T);

impl<'tcx, T> Visitor<'tcx> for TransferFunction<'_, T>
where
    T: GenKill<Local>,
{
    fn visit_place(&mut self, place: &mir::Place<'tcx>, context: PlaceContext, location: Location) {
        if let PlaceContext::MutatingUse(MutatingUseContext::Yield) = context {
            // The resume place is evaluated and assigned to only after generator resumes, so its
            // effect is handled separately in `yield_resume_effect`.
            return;
        }

        match DefUse::for_place(*place, context) {
            Some(DefUse::Def) => {
                if let PlaceContext::MutatingUse(
                    MutatingUseContext::Call | MutatingUseContext::AsmOutput,
                ) = context
                {
                    // For the associated terminators, this is only a `Def` when the terminator returns
                    // "successfully." As such, we handle this case separately in `call_return_effect`
                    // above. However, if the place looks like `*_5`, this is still unconditionally a use of
                    // `_5`.
                } else {
                    self.0.kill(place.local);
                }
            }
            Some(DefUse::Use) => self.0.gen_(place.local),
            None => {}
        }

        self.visit_projection(place.as_ref(), context, location);
    }

    fn visit_terminator(&mut self, terminator: &mir::Terminator<'tcx>, location: Location) {
        match &terminator.kind {
            _ => self.super_terminator(terminator, location),
        }
    }

    fn visit_local(&mut self, local: Local, context: PlaceContext, _: Location) {
        DefUse::apply(self.0, local.into(), context);
    }
}

#[derive(Eq, PartialEq, Clone)]
enum DefUse {
    Def,
    Use,
}

impl DefUse {
    fn apply(trans: &mut impl GenKill<Local>, place: Place<'_>, context: PlaceContext) {
        match DefUse::for_place(place, context) {
            Some(DefUse::Def) => trans.kill(place.local),
            Some(DefUse::Use) => trans.gen_(place.local),
            None => {}
        }
    }

    fn for_place(place: Place<'_>, context: PlaceContext) -> Option<DefUse> {
        match context {
            PlaceContext::NonUse(_) => None,

            PlaceContext::MutatingUse(
                MutatingUseContext::Call
                | MutatingUseContext::Yield
                | MutatingUseContext::AsmOutput
                | MutatingUseContext::Store
                | MutatingUseContext::Deinit,
            ) => {
                if place.is_indirect() {
                    // Treat derefs as a use of the base local. `*p = 4` is not a def of `p` but a
                    // use.
                    Some(DefUse::Use)
                } else if place.projection.is_empty() {
                    Some(DefUse::Def)
                } else {
                    None
                }
            }

            // Setting the discriminant is not a use because it does no reading, but it is also not
            // a def because it does not overwrite the whole place
            PlaceContext::MutatingUse(MutatingUseContext::SetDiscriminant) => {
                place.is_indirect().then_some(DefUse::Use)
            }

            // All other contexts are uses...
            PlaceContext::MutatingUse(
                MutatingUseContext::AddressOf
                | MutatingUseContext::Borrow
                | MutatingUseContext::Retag,
            )
            | PlaceContext::NonMutatingUse(
                NonMutatingUseContext::AddressOf
                | NonMutatingUseContext::Copy
                | NonMutatingUseContext::Inspect
                | NonMutatingUseContext::Move
                | NonMutatingUseContext::FakeBorrow
                | NonMutatingUseContext::SharedBorrow
                | NonMutatingUseContext::PlaceMention,
            ) => Some(DefUse::Use),
            PlaceContext::MutatingUse(MutatingUseContext::Drop) => None,

            PlaceContext::MutatingUse(MutatingUseContext::Projection)
            | PlaceContext::NonMutatingUse(NonMutatingUseContext::Projection) => {
                unreachable!("A projection could be a def or a use and must be handled separately")
            }
        }
    }
}
