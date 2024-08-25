use rustc_index::bit_set::ChunkedBitSet;
use rustc_middle::{
    mir::{
        self,
        visit::{MutatingUseContext, NonMutatingUseContext, PlaceContext, Visitor},
        CallReturnPlaces, Local, Location, Place, TerminatorEdges,
    },
    ty::TyCtxt,
};
use rustc_mir_dataflow::{
    move_paths::{HasMoveData, LookupResult, MoveData, MovePathIndex},
    on_all_children_bits, AnalysisDomain, Backward, GenKill, GenKillAnalysis, MoveDataParamEnv,
};

use crate::resolve::place_contains_borrow_deref;

/// A liveness analysis used for insertion of "resolve" statements.
/// It differs from Rustc's :
/// - It's based on move paths, and not on locals
/// - It ignores `drop`. This is meant to be used exclusively for `Resolve`.
///   FIXME: Replace this if any unsoundness seems to occur with borrows.
/// - Dereferencing boxes for writing is considered as a "Def". Dereferencing mutable
///   borrows for writing is still considered as a Use.
pub struct MaybeLiveExceptDrop<'a, 'tcx> {
    body: &'a mir::Body<'tcx>,
    mdpe: &'a MoveDataParamEnv<'tcx>,
    tcx: TyCtxt<'tcx>,
}

impl<'a, 'tcx> MaybeLiveExceptDrop<'a, 'tcx> {
    pub fn new(
        body: &'a mir::Body<'tcx>,
        mdpe: &'a MoveDataParamEnv<'tcx>,
        tcx: TyCtxt<'tcx>,
    ) -> Self {
        MaybeLiveExceptDrop { body, mdpe, tcx }
    }
}

impl<'a, 'tcx> AnalysisDomain<'tcx> for MaybeLiveExceptDrop<'a, 'tcx> {
    type Domain = ChunkedBitSet<MovePathIndex>;
    type Direction = Backward;

    const NAME: &'static str = "liveness-two";

    fn bottom_value(&self, _body: &mir::Body<'tcx>) -> Self::Domain {
        // bottom = not live
        ChunkedBitSet::new_empty(self.move_data().move_paths.len())
    }

    fn initialize_start_block(&self, _: &mir::Body<'tcx>, _: &mut Self::Domain) {
        // No variables are live until we observe a use
    }
}

impl<'a, 'tcx> HasMoveData<'tcx> for MaybeLiveExceptDrop<'a, 'tcx> {
    fn move_data(&self) -> &MoveData<'tcx> {
        &self.mdpe.move_data
    }
}

impl<'a, 'tcx> GenKillAnalysis<'tcx> for MaybeLiveExceptDrop<'a, 'tcx> {
    type Idx = MovePathIndex;

    fn domain_size(&self, _body: &mir::Body<'tcx>) -> usize {
        self.move_data().move_paths.len()
    }

    fn statement_effect(
        &mut self,
        trans: &mut impl GenKill<Self::Idx>,
        statement: &mir::Statement<'tcx>,
        location: Location,
    ) {
        TransferFunction(trans, self).visit_statement(statement, location);
    }

    fn terminator_effect<'mir>(
        &mut self,
        trans: &mut Self::Domain,
        terminator: &'mir mir::Terminator<'tcx>,
        location: Location,
    ) -> TerminatorEdges<'mir, 'tcx> {
        TransferFunction(trans, self).visit_terminator(terminator, location);
        terminator.edges()
    }

    fn call_return_effect(
        &mut self,
        trans: &mut Self::Domain,
        _block: mir::BasicBlock,
        return_places: CallReturnPlaces<'_, 'tcx>,
    ) {
        return_places.for_each(|place| {
            let du = if place_contains_borrow_deref(place.as_ref(), self.body, self.tcx) {
                // Treat derefs of (mutable) borrows as a use of the base local.
                //`*p = 4` is not a def of `p` but a use.
                DefUse::Use
            } else {
                DefUse::Def
            };
            du.apply(trans, &place, self.move_data())
        });
    }
}

struct TransferFunction<'a, 'tcx, T>(&'a mut T, &'a MaybeLiveExceptDrop<'a, 'tcx>);

impl<'a, 'tcx, T> Visitor<'tcx> for TransferFunction<'a, 'tcx, T>
where
    T: GenKill<MovePathIndex>,
{
    fn visit_place(&mut self, place: &mir::Place<'tcx>, context: PlaceContext, location: Location) {
        if matches!(
            context,
            PlaceContext::MutatingUse(
                MutatingUseContext::Call
                    | MutatingUseContext::Yield
                    | MutatingUseContext::AsmOutput,
            )
        ) {
            // For the associated terminators, we handle this case separately in
            // `call_return_effect` above.
            ()
        }

        DefUse::for_place(place, context, self.1).apply(self.0, place, &self.1.mdpe.move_data);

        // Visit indices of arrays/slices, which appear as locals
        self.visit_projection(place.as_ref(), context, location);
    }

    fn visit_local(&mut self, local: Local, context: PlaceContext, _: Location) {
        DefUse::for_place(&local.into(), context, self.1).apply(
            self.0,
            &local.into(),
            self.1.move_data(),
        )
    }
}

#[derive(Eq, PartialEq, Clone)]
enum DefUse {
    Def,
    Use,
    None,
}

impl DefUse {
    fn apply<'tcx>(
        self,
        trans: &mut impl GenKill<MovePathIndex>,
        place: &Place<'tcx>,
        md: &MoveData<'tcx>,
    ) {
        match self {
            DefUse::Def => {
                if let LookupResult::Exact(mp) = md.rev_lookup.find(place.as_ref()) {
                    on_all_children_bits(md, mp, |mpi| trans.kill(mpi));
                }
                // Is LookupResult::Parent even possible here??
                // It may appear for Index places ?
            }
            DefUse::Use => match md.rev_lookup.find(place.as_ref()) {
                LookupResult::Exact(mp) => on_all_children_bits(md, mp, |mpi| trans.gen_(mpi)),
                LookupResult::Parent(mp) => trans.gen_(mp.unwrap()),
            },
            DefUse::None => {}
        }
    }

    fn for_place<'tcx>(
        place: &Place<'tcx>,
        context: PlaceContext,
        ctx: &MaybeLiveExceptDrop<'_, 'tcx>,
    ) -> DefUse {
        match context {
            PlaceContext::NonUse(_) => DefUse::None,

            PlaceContext::MutatingUse(
                MutatingUseContext::Call
                | MutatingUseContext::Yield
                | MutatingUseContext::AsmOutput
                | MutatingUseContext::Store
                | MutatingUseContext::Deinit,
            ) => {
                if place_contains_borrow_deref(place.as_ref(), &ctx.body, ctx.tcx) {
                    // Treat derefs of (mutable) borrows as a use of the base local.
                    //`*p = 4` is not a def of `p` but a use.
                    DefUse::Use
                } else {
                    DefUse::Def
                }
            }

            // Setting the discriminant is not a use because it does no reading, but it is also not
            // a def because it does not overwrite the whole place
            PlaceContext::MutatingUse(MutatingUseContext::SetDiscriminant) => {
                if place_contains_borrow_deref(place.as_ref(), &ctx.body, ctx.tcx) {
                    DefUse::Use
                } else {
                    DefUse::None
                }
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
            ) => DefUse::Use,
            PlaceContext::MutatingUse(MutatingUseContext::Drop) => DefUse::None,

            PlaceContext::MutatingUse(MutatingUseContext::Projection)
            | PlaceContext::NonMutatingUse(NonMutatingUseContext::Projection) => {
                unreachable!("A projection could be a def or a use and must be handled separately")
            }
        }
    }
}
