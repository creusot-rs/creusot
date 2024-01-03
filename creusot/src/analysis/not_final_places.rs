use crate::extended_location::ExtendedLocation;
use rustc_index::bit_set::BitSet;
use rustc_middle::mir::{
    self, visit::Visitor, BasicBlock, Location, Place, PlaceRef, ProjectionElem, Statement,
    Terminator,
};
use rustc_mir_dataflow::{
    fmt::DebugWithContext, AnalysisDomain, Backward, GenKill, GenKillAnalysis, ResultsCursor,
};
use std::collections::HashMap;

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
#[derive(Debug)]
pub struct NotFinalPlaces<'tcx> {
    /// Mapping from a place to its ID
    ///
    /// This is necessary to use a `BitSet<PlaceId>`.
    places: HashMap<PlaceRef<'tcx>, PlaceId>,
    /// Used to ban unnesting (`**ref_ref_x = ...`)
    ///
    /// In practice, this means the underlying place has no `Deref`.
    has_indirection: BitSet<PlaceId>,
    /// Maps each place to the set of its subplaces.
    ///
    /// A `p1` is a subplace of `p2` if they refer to the same local variable, and
    /// `p2.projection` is a prefix of `p1.projection`.
    subplaces: Vec<Vec<PlaceRef<'tcx>>>,
    /// Maps each place to the set of conflicting subplaces.
    ///
    /// Two places `p1` and `p2` are conflicting if one is a subplace of the other.
    conflicting_places: Vec<Vec<PlaceRef<'tcx>>>,
}

impl<'tcx> NotFinalPlaces<'tcx> {
    pub fn new(body: &mir::Body<'tcx>) -> Self {
        struct VisitAllPlaces<'tcx>(HashMap<PlaceRef<'tcx>, PlaceId>);
        impl<'tcx> Visitor<'tcx> for VisitAllPlaces<'tcx> {
            fn visit_place(
                &mut self,
                place: &Place<'tcx>,
                _: mir::visit::PlaceContext,
                _: Location,
            ) {
                let place_ref = place.as_ref();
                for place in
                    std::iter::once(place_ref).chain(place_ref.iter_projections().map(|(p, _)| p))
                {
                    let idx = self.0.len();
                    if let std::collections::hash_map::Entry::Vacant(entry) = self.0.entry(place) {
                        entry.insert(idx);
                    }
                }
            }
        }

        let mut visitor = VisitAllPlaces(HashMap::new());
        visitor.visit_body(body);
        let places = visitor.0;
        let mut contains_dereference = BitSet::new_empty(places.len());
        let mut subplaces = vec![Vec::new(); places.len()];
        let mut conflicting_places = vec![Vec::new(); places.len()];
        for (place, id) in &places {
            if place.projection.get(1..).unwrap_or_default().contains(&ProjectionElem::Deref) {
                contains_dereference.insert(*id);
            }
            for (other_place, other_id) in &places {
                if id == other_id || place.local != other_place.local {
                    continue;
                }
                if other_place.projection.get(..place.projection.len()) == Some(place.projection) {
                    subplaces[*id].push(*other_place);
                    conflicting_places[*id].push(*other_place);
                    conflicting_places[*other_id].push(*place);
                }
            }
        }
        Self { places, has_indirection: contains_dereference, subplaces, conflicting_places }
    }

    /// Run the analysis right **after** `location`, and determines if `place` is a final reborrow.
    pub fn is_final_at(
        cursor: &mut ResultsCursor<'_, 'tcx, NotFinalPlaces<'tcx>>,
        place: &Place<'tcx>,
        location: Location,
    ) -> bool {
        let deref_position =
            match place.projection.iter().position(|p| matches!(p, ProjectionElem::Deref)) {
                Some(p) => p,
                // This is not a reborrow
                None => return false,
            };
        if place.projection[deref_position + 1..].contains(&ProjectionElem::Deref) {
            // unnesting
            return false;
        }

        ExtendedLocation::Start(location.successor_within_block()).seek_to(cursor);
        let analysis: &Self = cursor.analysis();

        let place_borrow = PlaceRef { local: place.local, projection: &place.projection };

        let id = analysis.places[&place_borrow];
        for place in std::iter::once(&place_borrow).chain(analysis.conflicting_places[id].iter()) {
            let id = analysis.places[place];
            if cursor.contains(id) {
                return false;
            }
        }
        true
    }
}

impl<'tcx> DebugWithContext<NotFinalPlaces<'tcx>> for BitSet<PlaceId> {}

impl<'tcx> AnalysisDomain<'tcx> for NotFinalPlaces<'tcx> {
    type Domain = BitSet<PlaceId>;

    type Direction = Backward;

    const NAME: &'static str = "not_final_places";

    fn bottom_value(&self, _: &mir::Body<'tcx>) -> Self::Domain {
        // start with every place "dead"
        BitSet::new_empty(self.places.len())
    }

    // no initialization, because we are doing backward analysis.
    fn initialize_start_block(&self, _: &mir::Body<'tcx>, _: &mut Self::Domain) {}
}

impl<'tcx> GenKillAnalysis<'tcx> for NotFinalPlaces<'tcx> {
    type Idx = PlaceId;

    fn statement_effect(
        &mut self,
        trans: &mut impl GenKill<Self::Idx>,
        statement: &Statement<'tcx>,
        location: Location,
    ) {
        PlaceVisitorKill { mapping: self, trans }.visit_statement(statement, location)
    }

    fn terminator_effect(
        &mut self,
        trans: &mut impl GenKill<Self::Idx>,
        terminator: &Terminator<'tcx>,
        location: Location,
    ) {
        PlaceVisitorKill { mapping: self, trans }.visit_terminator(terminator, location)
    }

    fn call_return_effect(
        &mut self,
        _trans: &mut impl GenKill<Self::Idx>,
        _block: BasicBlock,
        _return_places: rustc_mir_dataflow::CallReturnPlaces<'_, 'tcx>,
    ) {
    }

    // We use `before_*_effect` to ensure that reads are processed _before_ writes.
    fn before_statement_effect(
        &mut self,
        trans: &mut impl GenKill<Self::Idx>,
        statement: &mir::Statement<'tcx>,
        location: Location,
    ) {
        PlaceVisitorGen { mapping: self, trans }.visit_statement(statement, location)
    }

    fn before_terminator_effect(
        &mut self,
        trans: &mut impl GenKill<Self::Idx>,
        terminator: &mir::Terminator<'tcx>,
        location: Location,
    ) {
        PlaceVisitorGen { mapping: self, trans }.visit_terminator(terminator, location)
    }
}

struct PlaceVisitorGen<'a, 'tcx, T> {
    mapping: &'a NotFinalPlaces<'tcx>,
    trans: &'a mut T,
}
impl<'a, 'tcx, T> Visitor<'tcx> for PlaceVisitorGen<'a, 'tcx, T>
where
    T: GenKill<PlaceId>,
{
    fn visit_place(&mut self, place: &Place<'tcx>, context: mir::visit::PlaceContext, _: Location) {
        use mir::visit::{MutatingUseContext, PlaceContext};
        match context {
            // TODO: should we really accept _all_ nonmutating uses ?
            PlaceContext::NonMutatingUse(_)
            // Note that a borrow is considered a read
            | PlaceContext::MutatingUse(MutatingUseContext::Borrow) => {
                self.trans.gen(self.mapping.places[&place.as_ref()])
            }
            _ => {}
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
    fn visit_place(&mut self, place: &Place<'tcx>, context: mir::visit::PlaceContext, _: Location) {
        use mir::visit::{MutatingUseContext, PlaceContext};
        match context {
            PlaceContext::MutatingUse(MutatingUseContext::Drop | MutatingUseContext::Store) => {
                let id: usize = self.mapping.places[&place.as_ref()];
                if !self.mapping.has_indirection.contains(id) {
                    self.trans.kill(id);
                    // Now, kill all subplaces of this place
                    for subplace in self.mapping.subplaces[id].iter() {
                        let subplace_id: usize = self.mapping.places[subplace];
                        if !self.mapping.has_indirection.contains(subplace_id) {
                            self.trans.kill(subplace_id);
                        }
                    }
                }
            }
            _ => {}
        }
    }
}
