use rustc_index::bit_set::MixedBitSet;
use rustc_middle::{
    mir::{
        self, CallReturnPlaces, Local, Location, Place, TerminatorEdges,
        visit::{MutatingUseContext, NonMutatingUseContext, PlaceContext, Visitor},
    },
    ty::TyCtxt,
};
use rustc_mir_dataflow::{
    Analysis, Backward, GenKill,
    move_paths::{HasMoveData, LookupResult, MoveData, MovePathIndex},
    on_all_children_bits,
};

use super::resolve::place_contains_borrow_deref;

/// A liveness analysis used for insertion of "resolve" statements.
/// This is meant to be used exclusively for `Resolve`.
/// It differs from Rustc's:
/// - It's based on move paths, and not on locals
/// - It ignores `drop`. This is only sound if drop does never
///   modify a mutable borrow contained in the drop value.
///   For now, in Creusot, we do not support implementing Drop, and we assume that it
///   has no observable effect, so this is coherent with ignoring drop in this analysis.
///   If someday we want to support drop in some way, one solution is to ignore drop when
///   all the type parameters are [may_dangle], consider it as a use if none of the type
///   parameter is [may_dangle], and emit an error otherwise.
/// - Dereferencing boxes for writing is considered as a "Def". Dereferencing mutable
///   borrows for writing is still considered as a Use.
pub struct MaybeLiveExceptDrop<'a, 'tcx> {
    body: &'a mir::Body<'tcx>,
    move_data: &'a MoveData<'tcx>,
    tcx: TyCtxt<'tcx>,
}

impl<'a, 'tcx> MaybeLiveExceptDrop<'a, 'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>, body: &'a mir::Body<'tcx>, mdpe: &'a MoveData<'tcx>) -> Self {
        MaybeLiveExceptDrop { body, move_data: mdpe, tcx }
    }
}

impl<'a, 'tcx> HasMoveData<'tcx> for MaybeLiveExceptDrop<'a, 'tcx> {
    fn move_data(&self) -> &MoveData<'tcx> {
        &self.move_data
    }
}

impl<'a, 'tcx> Analysis<'tcx> for MaybeLiveExceptDrop<'a, 'tcx> {
    type Domain = MixedBitSet<MovePathIndex>;
    type Direction = Backward;

    const NAME: &'static str = "liveness-two";

    fn bottom_value(&self, _body: &mir::Body<'tcx>) -> Self::Domain {
        // bottom = not live
        MixedBitSet::new_empty(self.move_data().move_paths.len())
    }

    fn initialize_start_block(&self, _: &mir::Body<'tcx>, _: &mut Self::Domain) {
        // No variables are live until we observe a use
    }
    fn apply_primary_statement_effect(
        &self,
        trans: &mut Self::Domain,
        statement: &mir::Statement<'tcx>,
        location: Location,
    ) {
        TransferFunction(trans, self).visit_statement(statement, location);
    }

    fn apply_primary_terminator_effect<'mir>(
        &self,
        trans: &mut Self::Domain,
        terminator: &'mir mir::Terminator<'tcx>,
        location: Location,
    ) -> TerminatorEdges<'mir, 'tcx> {
        TransferFunction(trans, self).visit_terminator(terminator, location);
        terminator.edges()
    }

    fn apply_call_return_effect(
        &self,
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

        DefUse::for_place(place, context, self.1).apply(self.0, place, &self.1.move_data);

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
                | MutatingUseContext::Store,
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
                MutatingUseContext::RawBorrow
                | MutatingUseContext::Borrow
                | MutatingUseContext::Retag,
            )
            | PlaceContext::NonMutatingUse(
                NonMutatingUseContext::RawBorrow
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
