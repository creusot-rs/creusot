use crate::extended_location::ExtendedLocation;
use rustc_index::bit_set::BitSet;
use rustc_middle::{
    mir::{
        self, visit::Visitor, BasicBlock, Body, Location, Place, PlaceElem, PlaceRef,
        ProjectionElem, Statement, Terminator,
    },
    ty::TyCtxt,
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
pub struct NotFinalPlaces<'tcx> {
    tcx: TyCtxt<'tcx>,
    /// Mapping from a place to its ID
    ///
    /// This is necessary to use a `BitSet<PlaceId>`.
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
    has_dereference: BitSet<PlaceId>,
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
    pub fn new(tcx: TyCtxt<'tcx>, body: &mir::Body<'tcx>) -> Self {
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
        let mut has_dereference = BitSet::new_empty(places.len());
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
                if places_conflict(tcx, body, place, other_place) {
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
        let deref_position =
            match Self::place_get_first_deref(place.as_ref(), cursor.body(), cursor.analysis().tcx)
            {
                Some(p) => p,
                // `p` is not a reborrow
                None => return None,
            };
        let borrowed =
            PlaceRef { local: place.local, projection: &place.projection[deref_position + 1..] };
        if Self::has_indirection(borrowed, cursor.body(), cursor.analysis().tcx) {
            // some type of indirection
            // Examples:
            // - &mut **x  // unnesting
            // - &mut x[y] // runtime indexing
            return None;
        }

        ExtendedLocation::Start(location.successor_within_block()).seek_to(cursor);
        let analysis: &Self = cursor.analysis();

        let place_borrow = PlaceRef { local: place.local, projection: &place.projection };

        let id = analysis.places[&place_borrow];
        for place in std::iter::once(&place_borrow).chain(analysis.conflicting_places[id].iter()) {
            let id = analysis.places[place];
            if cursor.contains(id) {
                return None;
            }
        }
        Some(deref_position)
    }

    fn has_indirection(place: PlaceRef<'tcx>, body: &mir::Body<'tcx>, tcx: TyCtxt<'tcx>) -> bool {
        place.iter_projections().any(|(pl, proj)| match proj {
            ProjectionElem::Deref => !pl.ty(&body.local_decls, tcx).ty.is_box(),
            ProjectionElem::Index(_)
            | ProjectionElem::ConstantIndex { .. }
            | ProjectionElem::Subslice { .. }
            | ProjectionElem::OpaqueCast(_) => true,
            _ => false,
        })
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

/// Helper function for checking if two places conflict.
///
/// Common conflicting cases include:
/// - Both places are the same: `*a.b` and `*a.b`
/// - One place is a subplace of the other: `a.b.c` and `a.b`
/// - There is a runtime indirection: `a[i]` and `a[j]`
// FIXME: this is mostly copied from `rustc_borrowck::places_conflict`: it would be nice if the corresponding function would be public.
fn places_conflict<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    place1: PlaceRef<'tcx>,
    place2: PlaceRef<'tcx>,
) -> bool {
    if place1.local != place2.local {
        // We have proven the borrow disjoint - further projections will remain disjoint.
        return false;
    }

    place_components_conflict(tcx, body, place1, place2)
}

enum Overlap {
    /// Places components are garanteed disjoint (e.g. `a.b` and `a.c`)
    Disjoint,
    /// Places pass through different fields of an union: we consider this case to be a conflict.
    Arbitrary,
    /// Places components might lead to the same place (e.g. `a.b` and `a.b`, or `a[i]` and `a[j]`)
    EqualOrDisjoint,
}

fn place_components_conflict<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    place1: PlaceRef<'tcx>,
    place2: PlaceRef<'tcx>,
) -> bool {
    // loop invariant: borrow_c is always either equal to access_c or disjoint from it.
    for ((borrow_place, borrow_c), &access_c) in
        std::iter::zip(place1.iter_projections(), place2.projection)
    {
        // Borrow and access path both have more components.
        //
        // Examples:
        //
        // - borrow of `a.(...)`, access to `a.(...)`
        // - borrow of `a.(...)`, access to `b.(...)`
        //
        // Here we only see the components we have checked so
        // far (in our examples, just the first component). We
        // check whether the components being borrowed vs
        // accessed are disjoint (as in the second example,
        // but not the first).
        match place_projection_conflict(tcx, body, borrow_place, borrow_c, access_c) {
            Overlap::Arbitrary => {
                // We have encountered different fields of potentially
                // the same union - the borrow now partially overlaps.
                //
                // There is no *easy* way of comparing the fields
                // further on, because they might have different types
                // (e.g., borrows of `u.a.0` and `u.b.y` where `.0` and
                // `.y` come from different structs).
                return true;
            }
            Overlap::EqualOrDisjoint => {
                // This is the recursive case - proceed to the next element.
            }
            Overlap::Disjoint => {
                // We have proven the borrow disjoint - further
                // projections will remain disjoint.
                return false;
            }
        }
    }

    // One place is a subplace of the other, e.g. `a.b` and `a.b.c`.
    true
}

// Given that the bases of `elem1` and `elem2` are always either equal
// or disjoint (and have the same type!), return the overlap situation
// between `elem1` and `elem2`.
fn place_projection_conflict<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    pi1: PlaceRef<'tcx>,
    pi1_elem: PlaceElem<'tcx>,
    pi2_elem: PlaceElem<'tcx>,
) -> Overlap {
    match (pi1_elem, pi2_elem) {
        (ProjectionElem::Deref, ProjectionElem::Deref) => {
            // derefs (e.g., `*x` vs. `*x`) - recur.
            Overlap::EqualOrDisjoint
        }
        (ProjectionElem::OpaqueCast(_), ProjectionElem::OpaqueCast(_)) => {
            // casts to other types may always conflict irrespective of the type being cast to.
            Overlap::EqualOrDisjoint
        }
        (ProjectionElem::Field(f1, _), ProjectionElem::Field(f2, _)) => {
            if f1 == f2 {
                // same field (e.g., `a.y` vs. `a.y`) - recur.
                Overlap::EqualOrDisjoint
            } else {
                let ty = pi1.ty(body, tcx).ty;
                if ty.is_union() {
                    // Different fields of a union, we are basically stuck.
                    Overlap::Arbitrary
                } else {
                    // Different fields of a struct (`a.x` vs. `a.y`). Disjoint!
                    Overlap::Disjoint
                }
            }
        }
        (ProjectionElem::Downcast(_, v1), ProjectionElem::Downcast(_, v2)) => {
            if v1 == v2 {
                // same variant.
                Overlap::EqualOrDisjoint
            } else {
                // even if the two variants may occupy the same space, they are disjoint since they cannot be active at the same time. The same is _not_ true for unions.
                Overlap::Disjoint
            }
        }
        (
            ProjectionElem::Index(..),
            ProjectionElem::Index(..)
            | ProjectionElem::ConstantIndex { .. }
            | ProjectionElem::Subslice { .. },
        )
        | (
            ProjectionElem::ConstantIndex { .. } | ProjectionElem::Subslice { .. },
            ProjectionElem::Index(..),
        ) => {
            // Array indexes (`a[0]` vs. `a[i]`). They might overlap.
            Overlap::EqualOrDisjoint
        }
        (
            ProjectionElem::ConstantIndex { offset: o1, min_length: _, from_end: false },
            ProjectionElem::ConstantIndex { offset: o2, min_length: _, from_end: false },
        )
        | (
            ProjectionElem::ConstantIndex { offset: o1, min_length: _, from_end: true },
            ProjectionElem::ConstantIndex { offset: o2, min_length: _, from_end: true },
        ) => {
            if o1 == o2 {
                Overlap::EqualOrDisjoint
            } else {
                Overlap::Disjoint
            }
        }
        (
            ProjectionElem::ConstantIndex {
                offset: offset_from_begin,
                min_length: min_length1,
                from_end: false,
            },
            ProjectionElem::ConstantIndex {
                offset: offset_from_end,
                min_length: min_length2,
                from_end: true,
            },
        )
        | (
            ProjectionElem::ConstantIndex {
                offset: offset_from_end,
                min_length: min_length1,
                from_end: true,
            },
            ProjectionElem::ConstantIndex {
                offset: offset_from_begin,
                min_length: min_length2,
                from_end: false,
            },
        ) => {
            // both patterns matched so it must be at least the greater of the two
            let min_length = std::cmp::max(min_length1, min_length2);
            // `offset_from_end` can be in range `[1..min_length]`, 1 indicates the last
            // element (like -1 in Python) and `min_length` the first.
            // Therefore, `min_length - offset_from_end` gives the minimal possible
            // offset from the beginning
            if offset_from_begin >= min_length - offset_from_end {
                Overlap::EqualOrDisjoint
            } else {
                Overlap::Disjoint
            }
        }
        (
            ProjectionElem::ConstantIndex { offset, min_length: _, from_end: false },
            ProjectionElem::Subslice { from, to, from_end: false },
        )
        | (
            ProjectionElem::Subslice { from, to, from_end: false },
            ProjectionElem::ConstantIndex { offset, min_length: _, from_end: false },
        ) => {
            if (from..to).contains(&offset) {
                Overlap::EqualOrDisjoint
            } else {
                Overlap::Disjoint
            }
        }
        (
            ProjectionElem::ConstantIndex { offset, min_length: _, from_end: false },
            ProjectionElem::Subslice { from, .. },
        )
        | (
            ProjectionElem::Subslice { from, .. },
            ProjectionElem::ConstantIndex { offset, min_length: _, from_end: false },
        ) => {
            if offset >= from {
                Overlap::EqualOrDisjoint
            } else {
                Overlap::Disjoint
            }
        }
        (
            ProjectionElem::ConstantIndex { offset, min_length: _, from_end: true },
            ProjectionElem::Subslice { to, from_end: true, .. },
        )
        | (
            ProjectionElem::Subslice { to, from_end: true, .. },
            ProjectionElem::ConstantIndex { offset, min_length: _, from_end: true },
        ) => {
            if offset > to {
                Overlap::EqualOrDisjoint
            } else {
                Overlap::Disjoint
            }
        }
        (
            ProjectionElem::Subslice { from: f1, to: t1, from_end: false },
            ProjectionElem::Subslice { from: f2, to: t2, from_end: false },
        ) => {
            if f2 >= t1 || f1 >= t2 {
                Overlap::Disjoint
            } else {
                Overlap::EqualOrDisjoint
            }
        }
        (ProjectionElem::Subslice { .. }, ProjectionElem::Subslice { .. }) => {
            Overlap::EqualOrDisjoint
        }
        _ => panic!(
            "mismatched projections in place_element_conflict: {:?} and {:?}",
            pi1_elem, pi2_elem
        ),
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
        use mir::visit::{MutatingUseContext, NonMutatingUseContext, PlaceContext};
        match context {
            // Although they read the borrow, most `NonMutatingUse` are fine, because they can't influence the prophecized value.
            // The only non-mutating uses we need to consider are:
            // - `Move`: the borrow may be used somewhere else to change its prophecy.
            // - 'Copy': cannot be emitted for a mutable borrow
            PlaceContext::NonMutatingUse(NonMutatingUseContext::Move)
            // Note that a borrow triggers a gen
            // e.g.
            // ```rust
            // let bor = &mut x;
            // let r1 = &mut *bor;
            // // ...
            // let r2 = &mut *bor; // r1 is not final !
            // ```
            | PlaceContext::MutatingUse(MutatingUseContext::Borrow) => {
                self.trans.gen(self.mapping.places[&place.as_ref()])
            }
            PlaceContext::MutatingUse(MutatingUseContext::Store)
            | PlaceContext::MutatingUse(MutatingUseContext::Call)
            | PlaceContext::MutatingUse(MutatingUseContext::SetDiscriminant)
            | PlaceContext::MutatingUse(MutatingUseContext::AsmOutput) => {
                let id = self.mapping.places[&place.as_ref()];
                if self.mapping.has_dereference.contains(id) {
                    // We are writing under a dereference, so this changes the prophecy of the underlying borrow. 
                    self.trans.gen(id);
                }
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
            PlaceContext::MutatingUse(
                MutatingUseContext::Store
                | MutatingUseContext::Call
                // Technically true, but unsupported by Creusot anyways
                | MutatingUseContext::AsmOutput,
            ) => {
                let id: usize = self.mapping.places[&place.as_ref()];
                self.trans.kill(id);
                // Now, kill all subplaces of this place
                for subplace in self.mapping.subplaces[id].iter() {
                    let subplace_id: usize = self.mapping.places[subplace];
                    self.trans.kill(subplace_id);
                }
            }
            _ => {}
        }
    }
}
