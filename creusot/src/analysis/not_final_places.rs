use crate::extended_location::ExtendedLocation;
use rustc_borrowck::consumers::PlaceConflictBias;
use rustc_index::bit_set::ChunkedBitSet;
use rustc_middle::{
    mir::{
        self,
        visit::{MutatingUseContext, NonMutatingUseContext, PlaceContext, Visitor},
        BasicBlock, CallReturnPlaces, Location, Place, PlaceRef, ProjectionElem, Statement,
        Terminator, TerminatorEdges,
    },
    ty::TyCtxt,
};
use rustc_mir_dataflow::{
    fmt::DebugWithContext, AnalysisDomain, Backward, GenKill, GenKillAnalysis, ResultsCursor,
};
use std::collections::{hash_map, HashMap};

pub type PlaceId = usize;

/// Analysis to determine "final" reborrows.
///
/// # Final borrows
///
/// A reborrow is considered final if the prophecy of the original borrow depends only on the reborrow.
/// In that case, the reborrow id can be inherited:
/// - If this is a reborrow of the same place (e.g. `let y = &mut *x`), the new id is the same.
/// - Else (e.g. `let y = &mut x.field`), the new id is deterministically derived from the old.
///
/// # Example Usage
///
/// Note that this analysis determines places that are **not** final.
///
/// ```rust,ignore
/// let tcx: rustc_middle::ty::TyCtxt = /* */;
/// let body: rustc_middle::mir::Body = /* */;
/// let mut not_final_places = NotFinalPlaces::new(body)
///     .into_engine(tcx, body)
///     .iterate_to_fixpoint()
///     .into_results_cursor(body);
/// /*
///     ...
/// */
/// let place: rustc_middle::mir::Place = /* place that we want to reborrow from */;
/// let location: rustc_middle::mir::Location = /* location of the reborrow in the MIR body */;
/// let is_final = NotFinalPlaces::is_final_at(not_final_borrows, place, location);
/// ```
pub struct NotFinalPlaces<'tcx> {
    tcx: TyCtxt<'tcx>,
    /// Mapping from a place to its ID
    ///
    /// This is necessary to use a `ChunkedBitSet<PlaceId>`.
    places: HashMap<PlaceRef<'tcx>, PlaceId>,
    /// Contains the places that dereference a mutable ref.
    ///
    /// For example,
    /// ```ignore
    /// let x: &mut T = /* ... */;
    /// *x;       // has dereference
    /// x.field;  // has dereference
    /// let y: Box<T> = /* ... */;
    /// *y;       // does not have dereference
    /// y.field;  // does not have dereference
    /// ```
    has_dereference: ChunkedBitSet<PlaceId>,
    /// Maps each place to the set of its subplaces.
    ///
    /// A `p1` is a subplace of `p2` if they refer to the same local variable, and
    /// `p2.projection` is a prefix of `p1.projection`.
    subplaces: Vec<Vec<PlaceRef<'tcx>>>,
    /// Maps each place to the set of conflicting subplaces.
    ///
    /// Two places `p1` and `p2` are conflicting if they may refer to the same memory location
    conflicting_places: Vec<Vec<PlaceRef<'tcx>>>,
}

impl<'tcx> NotFinalPlaces<'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>, body: &mir::Body<'tcx>) -> Self {
        struct VisitAllPlaces<'tcx> {
            places: HashMap<PlaceRef<'tcx>, PlaceId>,
        }
        impl<'tcx> Visitor<'tcx> for VisitAllPlaces<'tcx> {
            fn visit_place(&mut self, place: &Place<'tcx>, context: PlaceContext, _: Location) {
                let place_ref = place.as_ref();
                // This is both an optimization, and required for `rustc_borrowck::consumers::places_conflict` to not crash.
                // This is ok to do, because those are places we will not consider anyways.
                if !(place_context_gen(context)
                    || place_context_gen_deref(context)
                    || place_context_kill(context))
                {
                    return;
                }
                for place in
                    std::iter::once(place_ref).chain(place_ref.iter_projections().map(|(p, _)| p))
                {
                    let idx = self.places.len();
                    if let hash_map::Entry::Vacant(entry) = self.places.entry(place) {
                        entry.insert(idx);
                    }
                }
            }
        }

        let mut visitor = VisitAllPlaces { places: HashMap::new() };
        visitor.visit_body(body);
        let places = visitor.places;
        let mut has_dereference = ChunkedBitSet::new_empty(places.len());
        let mut subplaces = vec![Vec::new(); places.len()];
        let mut conflicting_places = vec![Vec::new(); places.len()];

        for (&place, &id) in &places {
            if Self::place_get_first_deref(place, body, tcx).is_some() {
                has_dereference.insert(id);
            }
            for (&other_place, &other_id) in &places {
                if id == other_id || place.local != other_place.local {
                    continue;
                }
                if other_place.projection.get(..place.projection.len()) == Some(place.projection) {
                    subplaces[id].push(other_place);
                }

                // We use `PlaceConflictBias::Overlap`, because we assume that unknown index accesses _do_ overlap.

                // This function would crash if `place` is a `*x` where `x: &T`.
                // But we filtered such places in the visitor.
                if rustc_borrowck::consumers::places_conflict(
                    tcx,
                    body,
                    place.to_place(tcx),
                    other_place.to_place(tcx),
                    PlaceConflictBias::Overlap,
                ) {
                    conflicting_places[id].push(other_place);
                }
            }
        }
        Self { tcx, places, has_dereference, subplaces, conflicting_places }
    }

    /// Run the analysis right **after** `location`, and determines if the borrow of
    /// `place` is a final reborrow.
    ///
    /// # Returns
    /// - If the reborrow is final, return the position of the dereference of the
    /// original borrow in `place.projection`.
    ///
    ///   For example, if the reborrow `&mut (*x.0)` is final, then the projections are
    /// `[Field(0), Deref]`, and so we return `Some(1)`.
    ///
    ///   `Deref` of a box is not considered as a dereference of a borrow.
    /// - Else, return `None`.
    pub fn is_final_at(
        cursor: &mut ResultsCursor<'_, 'tcx, Self>,
        place: &Place<'tcx>,
        location: Location,
    ) -> Option<usize> {
        let body = cursor.body();
        let tcx = cursor.analysis().tcx;

        let deref_position = match Self::place_get_first_deref(place.as_ref(), body, tcx) {
            Some(p) => p,
            // `p` is not a reborrow
            None => return None,
        };
        if place.iter_projections().skip(deref_position + 1).any(|(pl, proj)| match proj {
            ProjectionElem::Deref => !pl.ty(body, tcx).ty.is_box(),
            ProjectionElem::Index(_)
            | ProjectionElem::ConstantIndex { .. }
            | ProjectionElem::Subslice { .. }
            | ProjectionElem::OpaqueCast(_) => true,
            _ => false,
        }) {
            // some type of indirection
            // Examples:
            // - &mut **x  // unnesting
            // - &mut x[y] // runtime indexing
            return None;
        }

        ExtendedLocation::Start(location.successor_within_block()).seek_to(cursor);
        let analysis: &Self = cursor.analysis();

        let id = analysis.places[&place.as_ref()];
        for place in std::iter::once(&place.as_ref()).chain(analysis.conflicting_places[id].iter())
        {
            let id = analysis.places[place];
            if cursor.contains(id) {
                return None;
            }
        }
        Some(deref_position)
    }

    /// Helper function: gets the index of the first projection of `place` that is a deref,
    /// but not a deref of a box.
    fn place_get_first_deref(
        place: PlaceRef<'tcx>,
        body: &mir::Body<'tcx>,
        tcx: TyCtxt<'tcx>,
    ) -> Option<usize> {
        place.iter_projections().position(|(pl, proj)| {
            proj == ProjectionElem::Deref && !pl.ty(&body.local_decls, tcx).ty.is_box()
        })
    }
}

impl<'tcx> DebugWithContext<NotFinalPlaces<'tcx>> for ChunkedBitSet<PlaceId> {}

impl<'tcx> AnalysisDomain<'tcx> for NotFinalPlaces<'tcx> {
    type Domain = ChunkedBitSet<PlaceId>;

    type Direction = Backward;

    const NAME: &'static str = "not_final_places";

    fn bottom_value(&self, _: &mir::Body<'tcx>) -> Self::Domain {
        // start with every place "dead"
        ChunkedBitSet::new_empty(self.places.len())
    }

    // no initialization, because we are doing backward analysis.
    fn initialize_start_block(&self, _: &mir::Body<'tcx>, _: &mut Self::Domain) {}
}

// The NotFinalPlaces analysis computes, for each location, places which either:
// - do not contain a mutable borrow deref and may be moved or borrowed in the future
//      i.e., if such a place contains a borrow, then this borrow may be written to before its resolution
// - do contain one or more mutable borrow deref, and may be written to in the future

impl<'tcx> GenKillAnalysis<'tcx> for NotFinalPlaces<'tcx> {
    type Idx = PlaceId;

    fn statement_effect(
        &mut self,
        trans: &mut impl GenKill<Self::Idx>,
        statement: &Statement<'tcx>,
        location: Location,
    ) {
        PlaceVisitorKill { mapping: self, trans }.visit_statement(statement, location);
        PlaceVisitorGen { mapping: self, trans }.visit_statement(statement, location);
    }

    fn terminator_effect<'mir>(
        &mut self,
        trans: &mut Self::Domain,
        terminator: &'mir Terminator<'tcx>,
        location: Location,
    ) -> TerminatorEdges<'mir, 'tcx> {
        PlaceVisitorKill { mapping: self, trans }.visit_terminator(terminator, location);
        PlaceVisitorGen { mapping: self, trans }.visit_terminator(terminator, location);
        terminator.edges()
    }

    fn call_return_effect(
        &mut self,
        _trans: &mut Self::Domain,
        _block: BasicBlock,
        _return_places: CallReturnPlaces<'_, 'tcx>,
    ) {
    }

    fn domain_size(&self, _: &mir::Body<'tcx>) -> usize {
        self.places.len()
    }
}

/// Determine when a place should be unconditionnaly 'gen'ed' in the analysis
fn place_context_gen(context: PlaceContext) -> bool {
    match context {
        // Although they read the borrow, most `NonMutatingUse` are fine, because they can't influence the prophecized value.
        // The only non-mutating uses we need to consider are:
        // - `Move`: the borrow may be used somewhere else to change its value.
        // - 'Copy': cannot be emitted for a mutable borrow
        PlaceContext::NonMutatingUse(NonMutatingUseContext::Move)
        // Note that a borrow triggers a gen
        // e.g.
        // ```rust
        // let bor = &mut x;
        // let r1 = &mut *bor;
        // // ...
        // let r2 = &mut bor; // r1 is not final !
        // ```
        | PlaceContext::MutatingUse(MutatingUseContext::Borrow) => true,
        _ => false,
    }
}
/// Determine when a place should be 'gen'ed' in the analysis. The caller should then also
/// check that the write occurs under a dereference.
fn place_context_gen_deref(context: PlaceContext) -> bool {
    match context {
        PlaceContext::MutatingUse(MutatingUseContext::Store)
        | PlaceContext::MutatingUse(MutatingUseContext::Call)
        | PlaceContext::MutatingUse(MutatingUseContext::SetDiscriminant)
        | PlaceContext::MutatingUse(MutatingUseContext::AsmOutput) => true,
        _ => false,
    }
}
/// Determine when a place should be 'killed' in the analysis
fn place_context_kill(context: PlaceContext) -> bool {
    matches!(
        context,
        PlaceContext::MutatingUse(
            MutatingUseContext::Store
            | MutatingUseContext::Call
            // Technically true, but unsupported by Creusot anyways
            | MutatingUseContext::AsmOutput,
        )
    )
}

struct PlaceVisitorGen<'a, 'tcx, T> {
    mapping: &'a NotFinalPlaces<'tcx>,
    trans: &'a mut T,
}
impl<'a, 'tcx, T> Visitor<'tcx> for PlaceVisitorGen<'a, 'tcx, T>
where
    T: GenKill<PlaceId>,
{
    fn visit_place(&mut self, place: &Place<'tcx>, context: PlaceContext, _: Location) {
        if place_context_gen(context) {
            self.trans.gen_(self.mapping.places[&place.as_ref()])
        } else if place_context_gen_deref(context) {
            let id = self.mapping.places[&place.as_ref()];
            if self.mapping.has_dereference.contains(id) {
                // We are writing under a dereference, so this changes the prophecy of the underlying borrow.
                self.trans.gen_(id);
            }
        }
    }
}

struct PlaceVisitorKill<'a, 'tcx, T> {
    mapping: &'a NotFinalPlaces<'tcx>,
    trans: &'a mut T,
}
impl<'a, 'tcx, T> Visitor<'tcx> for PlaceVisitorKill<'a, 'tcx, T>
where
    T: GenKill<PlaceId>,
{
    fn visit_place(&mut self, place: &Place<'tcx>, context: PlaceContext, _: Location) {
        if place_context_kill(context) {
            let id: usize = self.mapping.places[&place.as_ref()];
            self.trans.kill(id);
            // Now, kill all subplaces of this place
            for subplace in self.mapping.subplaces[id].iter() {
                let subplace_id: usize = self.mapping.places[subplace];
                self.trans.kill(subplace_id);
            }
        }
    }
}
